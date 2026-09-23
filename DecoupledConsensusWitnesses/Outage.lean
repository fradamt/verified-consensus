module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ReviewTheorem
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public meta import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public meta import DecoupledConsensusModel.Protocol.Handlers
public meta import DecoupledConsensusStatements.Instantiation.Proposals
public meta import DecoupledConsensusInternal.Definitions.NamedStableChainOutage
public meta import DecoupledConsensusModel.Execution.Setup
public meta import DecoupledConsensusInternal.Legacy.Definitions.LeakFairnessL1
public meta import DecoupledConsensusInternal.Legacy.Definitions.ActionSources

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Weak-participation GST-zero witness

This file starts the concrete `Fin 2` run used for the weak-genesis branches. The
single honest validator is `0`; validator `1` is Byzantine and is silent.
The run ticks the honest validator at every public time through time `45`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000



namespace DecoupledConsensusModel
namespace Witnesses
namespace Outage

open Internal Execution Statements Internal.NamedOutageEntry Internal.NamedStableChainOutage

def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 44
  t_GST_nonneg := by norm_num
  proposer := fun s => if s = 1 then 0 else 1
  committees := ⟨fun _ => {0}⟩
  electorate :=
    { weight := fun v => if v = 0 then 3 else 1
      weight_pos := by
        intro v
        by_cases h : v = 0 <;> simp [h] }

def hc : Protocol.HealConfig where
  R := 3
  R_ge_three := by norm_num
  η_SG := 2
  η_SG_ge_one := by norm_num

def cfg : Protocol.HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 6
  K_ge_four := by norm_num
  D_ge_two := by norm_num

def node (v : Fin 2) : Protocol.Node (Fin 2) :=
  { val_index := v
    new_root := fun s => ⟨s + 1⟩
    awake := fun _ => v = 0 }

def S : Setup (Fin 2) where
  E := E
  hc := hc
  cfg := cfg
  node := node
  node_val_index := by intro v; rfl
  timeout_rounds := by decide
  committee_nonempty := by
    intro s
    change ({0} : Finset (Fin 2)).Nonempty
    simp
  outage_window := by decide

def events : List (Event (Fin 2)) :=
  (List.range 46).map (fun n => .tick 0 (n : Time))

def rho : Run (Fin 2) :=
  { honest := {0}
    horizon := 45
    events := events }

theorem gst_eq_44 : S.E.t_GST = 44 := rfl

theorem horizon_eq : rho.horizon = 45 := rfl

/-!
The executable run has 46 ticks, at times `0` through `45`. Its nonempty
emission prefixes are: proposals at `4, 8, 12, 16, 20, 24, 28`; Goldfish
votes at `5, 9, 13, 17, 21, 25, 29`; and round-action attestations at `6,
18, 30`. The proposal roots are `2` through `8`. Thus round `0` is covered
by the real slot-`1` proposal, and later blocks also exercise carried GF and
attestation payloads.
-/

/-! ## Primitive schedule and participant facts -/

theorem honest_eq : rho.honest = ({0} : Finset (Fin 2)) := rfl

theorem honest_nonempty : rho.honest.Nonempty := by
  change ({0} : Finset (Fin 2)).Nonempty
  exact ⟨0, by simp⟩

theorem byzantine_nonempty : (Finset.univ \ rho.honest).Nonempty := by
  change (Finset.univ \ ({0} : Finset (Fin 2))).Nonempty
  exact ⟨1, by simp⟩

theorem event_mem_shape {e : Event (Fin 2)} (he : e ∈ rho.events) :
    ∃ n : Nat, n < 46 ∧ e = .tick 0 (n : Time) := by
  change e ∈ (List.range 46).map (fun n : Nat => .tick 0 (n : Time)) at he
  obtain ⟨n, hn, hne⟩ := List.mem_map.mp he
  exact ⟨n, by simpa using hn, hne.symm⟩

theorem schedule_sorted : rho.events.Pairwise
    (fun e f => NamedEvent.key e ≤ NamedEvent.key f) := by
  change ((List.range 46).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time))).Pairwise
    (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
  rw [List.pairwise_map]
  have hrange : ∀ n : Nat, (List.range n).Pairwise (fun a b => a ≤ b) := by
    intro n
    induction n with
    | zero => exact List.Pairwise.nil
    | succ n ih =>
        rw [List.range_succ, List.pairwise_append]
        refine ⟨ih, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact (List.mem_range.mp ha).le
  refine (hrange 46).imp ?_
  intro n m hnm
  rcases Nat.lt_or_eq_of_le hnm with hlt | rfl
  · simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase,
      Prod.Lex.toLex_le_toLex, hlt]
  · simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase]

theorem schedule_nodup : rho.events.Nodup := by
  change ((List.range 46).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time))).Nodup
  apply (List.nodup_range : (List.range 46).Nodup).map
  intro n m h
  have hnm : (n : Time) = (m : Time) := congrArg NamedEvent.time h
  exact_mod_cast hnm

theorem schedule_in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := event_mem_shape he
  change 0 ≤ (n : Time) ∧ (n : Time) ≤ (45 : Time)
  constructor
  · exact_mod_cast (Nat.zero_le n)
  · exact_mod_cast (Nat.le_of_lt_succ hn)

theorem schedule_honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := event_mem_shape he
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem schedule_tick_public : ∀ v t, .tick v t ∈ rho.events → PublicTime S t := by
  intro v t he
  obtain ⟨n, hn, hne⟩ := event_mem_shape he
  cases hne
  exact ⟨n, by norm_num [PublicTime, S, E]⟩

theorem schedule_tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime S t →
    0 ≤ t → t ≤ rho.horizon → .tick v t ∈ rho.events := by
  intro v hv t ht hnonneg hhor
  have hv0 : v = 0 := by
    change v ∈ ({0} : Finset (Fin 2)) at hv
    simpa using hv
  subst v
  rcases ht with ⟨n, hn⟩
  have hnt : t = (n : Time) := by simpa [S, E] using hn
  have hn46 : n < 46 := by
    rw [hnt] at hhor
    change (n : Time) ≤ 45 at hhor
    have hn30 : n ≤ 45 := by exact_mod_cast hhor
    nlinarith
  rw [hnt]
  exact List.mem_map.mpr ⟨n, by simpa using hn46, rfl⟩

theorem delivery_wire : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.wellFormed S o = true := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? he)
  cases hne

theorem delivery_deps : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.depsPresent (NamedRun.stateBefore S rho i v).st o = true := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? he)
  cases hne

theorem delivery_fresh : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o = false := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? he)
  cases hne

theorem schedule_well_formed : NamedScheduleWellFormed S rho where
  horizon_nonneg := by decide
  sorted := schedule_sorted
  nodup := schedule_nodup
  in_horizon := schedule_in_horizon
  honest_only := schedule_honest_only
  tick_public := schedule_tick_public
  tick_total := schedule_tick_total

theorem objects_empty : NamedRun.objects rho = [] := by
  change ((List.range 46).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time))).filterMap
      NamedEvent.object? = []
  simp [NamedEvent.object?]

theorem event_at_is_tick {i : Nat} {e : Event (Fin 2)}
    (he : rho.events[i]? = some e) : ∃ n : Nat, n < 46 ∧ e = .tick 0 (n : Time) := by
  exact event_mem_shape (List.mem_of_getElem? he)

theorem accepted_block_is_emitted {i : Nat} {B : NamedBlock (Fin 2)} {t : Time}
    (h : NamedRun.acceptsAt S rho i 0 (.block B) t) :
    ∃ t' : Time, NamedRun.emits S rho 0 (.block B) t' := by
  obtain ⟨hactual, hpre, hpost⟩ := h
  obtain ⟨e, he, hnode, htime⟩ := hactual.2
  have hevent := event_at_is_tick he
  have hindex := hactual.1
  change NamedRun.processesAtIndex S rho i 0 (.block B) at hindex
  rcases hindex with ⟨te, htick, hmem⟩ | ⟨td, hdeliver⟩
  · exact ⟨te, ⟨i, htick, hmem⟩⟩
  · obtain ⟨n, hn, hne⟩ := hevent
    have hbad : (NamedEvent.tick (0 : Fin 2) (n : Time)) =
        NamedEvent.deliver 0 (.block B) td := by
      exact hne.symm.trans (Option.some.inj (he.symm.trans hdeliver))
    cases hbad

theorem emitted_block_shape_local {B : NamedBlock (Fin 2)} {t : Time}
    (h : NamedRun.emits S rho 0 (.block B) t) :
    0 < B.slot ∧ t = Protocol.proposal_time S.E B.slot ∧
      S.E.proposer B.slot = 0 :=
  Proofs.HealingSurface.emits_block_shape S rho h

theorem proposal_root_of_output
    (contract : Protocol.GradeContract (Fin 2))
    (st : Protocol.NamedStore (Fin 2)) {B : NamedBlock (Fin 2)}
    (hB : (Protocol.NamedDuties.propose_block_with contract S.E S.hc S.cfg
      (S.node 0) st).2 = some B) :
    B.root = (S.node 0).new_root st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with at hB
  generalize hP : Protocol.NamedActions.proposal_with contract .poolAndCarried
    S.E S.hc (S.node 0) st = P at hB
  cases P with
  | none => simp at hB
  | some X =>
      simp at hB
      subst B
      have hroot := congrArg (Option.map NamedBlock.root) hP
      rcases (by
        simpa [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input] using hroot) with
        ⟨a, ha, hax⟩
      simpa using hax.symm

theorem emitted_block_root_local {B : NamedBlock (Fin 2)} {t : Time}
    (h : NamedRun.emits S rho 0 (.block B) t) :
    B.root = ⟨B.slot + 1⟩ := by
  obtain ⟨i, hi, hmem⟩ := h
  have hdetails :=
    Proofs.HealingSurface.block_mem_on_tick_emit S 0
      (NamedRun.stateBefore S rho i 0) t hmem
  have hB := hdetails.2
  have hroot := proposal_root_of_output _ _ hB
  have hslot := Proofs.HealingSurface.propose_block_with_slot _ _ _ _ _ _ hB
  rw [hroot, ← hslot]
  rfl

theorem named_ancestor_mem_local {st : Protocol.NamedStore (Fin 2)}
    (hpc : Proofs.NamedStore.NamedParentClosed st) {A B : NamedBlock (Fin 2)}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      have hA : A = NamedBlock.genesis := by
        simpa [NamedBlock.Preceq, NamedBlock.preceq] using hAB
      simpa [hA] using hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with hEq | hParent
      · simpa [hEq] using hB
      · exact ih (hpc.2 _ hB) hParent

theorem run_block_origin {B : NamedBlock (Fin 2)}
    (hB : NamedRun.blockInRun S rho B) :
    B = NamedBlock.genesis ∨ ∃ t : Time, NamedRun.emits S rho 0 (.block B) t := by
  rcases hB with ⟨C, hC, hBC⟩
  rcases hC with hobjects | ⟨v, hv, i, hCbody⟩
  · rw [objects_empty] at hobjects
    simp at hobjects
  · have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    subst v
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
        (NamedRun.stateBefore S rho i 0).st :=
      (Proofs.NamedRuntime.stateBefore_invariants S rho i 0).1.1.1
    have hBbody := named_ancestor_mem_local hcoh.2.2.1 hCbody hBC
    rcases Proofs.NamedOutageProvenance.held_block_origin S rho i 0 hBbody with
      hgen | ⟨j, hj, t, hacc⟩
    · exact Or.inl hgen
    · exact Or.inr (accepted_block_is_emitted hacc)

theorem emitted_node_zero {v : Fin 2} {o : NamedObject (Fin 2)} {t : Time}
    (h : NamedRun.emits S rho v o t) : v = 0 := by
  obtain ⟨i, hi, ho⟩ := h
  obtain ⟨n, hn, hne⟩ := event_at_is_tick hi
  exact congrArg NamedEvent.node hne

theorem root_collision_free : RootCollisionFree S rho where
  root_injective B C hB hC A D hAB hDC hroot := by
    have collision_of_runs : ∀ {A D : NamedBlock (Fin 2)},
        NamedRun.blockInRun S rho A → NamedRun.blockInRun S rho D →
        A.root = D.root → A = D := by
      intro A D hArun hDrun hroot
      rcases run_block_origin hArun with hAgen | ⟨tA, hAemit⟩
      · rcases run_block_origin hDrun with hDgen | ⟨tD, hDemit⟩
        · simp [hAgen, hDgen]
        · rw [hAgen, emitted_block_root_local hDemit] at hroot
          have hval : (0 : Nat) = D.slot + 1 := by
            simpa [NamedBlock.root, genesisRoot] using congrArg BlockId.value hroot
          exact False.elim (Nat.noConfusion hval)
      · rcases run_block_origin hDrun with hDgen | ⟨tD, hDemit⟩
        · rw [hDgen, emitted_block_root_local hAemit] at hroot
          have hval : A.slot + 1 = (0 : Nat) := by
            simpa [NamedBlock.root, genesisRoot] using congrArg BlockId.value hroot
          exact False.elim (Nat.noConfusion hval)
        · have hval := congrArg BlockId.value
            ((emitted_block_root_local hAemit).symm.trans
              (hroot.trans (emitted_block_root_local hDemit)))
          have hslot : A.slot = D.slot := by simpa using hval
          exact Proofs.HealingSurface.emits_block_unique S schedule_well_formed
            hAemit hDemit hslot
    rcases hAB with hAB | hAC
    · rcases hDC with hDB | hDC
      · exact collision_of_runs
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hAB)
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hDB) hroot
      · exact collision_of_runs
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hAB)
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hDC) hroot

    · rcases hDC with hDB | hDC
      · exact collision_of_runs
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hAC)
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hDB) hroot
      · exact collision_of_runs
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hAC)
          (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hDC) hroot

/-! ## Run-local provenance helpers -/

theorem emits_at_tick_index {i : Nat} {t : Time} {o : NamedObject (Fin 2)}
    (hi : rho.events[i]? = some (.tick 0 t))
    (hemit : NamedRun.emits S rho 0 o t) :
    o ∈ NamedRun.emittedAt S rho i 0 t := by
  obtain ⟨j, hj, hmem⟩ := hemit
  obtain ⟨hil, hieval⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hjeval⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff schedule_nodup).mp (by rw [hieval, hjeval])
  subst j
  exact hmem

theorem processes_is_emission {o : NamedObject (Fin 2)} {t : Time}
    (h : NamedRun.processes S rho 0 o t) : NamedRun.emits S rho 0 o t := by
  rcases h with h | ⟨i, hi⟩
  · exact h
  · obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? hi)
    have hbad : NamedEvent.tick (0 : Fin 2) (n : Time) =
        NamedEvent.deliver 0 o t := by
      exact hne.symm
    cases hbad

theorem event_time_eq_index {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t)) : t = (i : Time) := by
  change ((List.range 46).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time)))[i]? =
    some (.tick 0 t) at hi
  obtain ⟨hil, hget⟩ := List.getElem?_eq_some_iff.mp hi
  have hget' : NamedEvent.tick (0 : Fin 2) (i : Time) =
      NamedEvent.tick 0 t := by
    simpa using hget
  exact congrArg NamedEvent.time hget'.symm

theorem honest_gf_pool_origin :
    ∀ (i : Nat) (k : Slot) (u : GoldfishVote (Fin 2)),
      u ∈ (NamedRun.stateBefore S rho i 0).st.core.gf_votes k →
      ∃ j, j < i ∧ ∃ t : Time,
        rho.events[j]? = some (.tick 0 t) ∧
          NamedRun.emits S rho 0 (.gfVote u) t := by
  intro i
  induction i with
  | zero =>
      intro k u hu
      simp [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
        Protocol.NamedStore.initial, Protocol.Store.init] at hu
  | succ i ih =>
      intro k u hu
      have hstep : NamedRun.stateBefore S rho (i + 1) =
          (rho.events[i]?.toList).foldl (NamedWorld.step S)
            (NamedRun.stateBefore S rho i) := by
        exact Proofs.NamedRuntime.stateBefore_succ S rho i
      cases he : rho.events[i]? with
      | none =>
          have hsame : NamedRun.stateBefore S rho (i + 1) 0 =
              NamedRun.stateBefore S rho i 0 := by
            rw [hstep, he]
            rfl
          rw [hsame] at hu
          obtain ⟨j, hj, t, htick, hem⟩ := ih k u hu
          exact ⟨j, Nat.lt_succ_of_lt hj, t, htick, hem⟩
      | some e =>
          obtain ⟨n, hn, hne⟩ := event_at_is_tick he
          subst e
          have hstate : NamedRun.stateBefore S rho (i + 1) 0 =
              (NamedNode.tick S 0 (NamedRun.stateBefore S rho i 0) (n : Time)).1 := by
            exact Proofs.NamedRuntime.stateBefore_tick S rho he
          obtain ⟨gc, hgcState, hgcEmit⟩ :
              ∃ gc : Protocol.GradeContract (Fin 2),
                (NamedNode.tick S 0 (NamedRun.stateBefore S rho i 0) (n : Time)).1.st =
                  (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node 0)
                    (NamedRun.stateBefore S rho i 0).st
                    (NamedRun.stateBefore S rho i 0).record (n : Time)).1 ∧
                (NamedNode.tick S 0 (NamedRun.stateBefore S rho i 0) (n : Time)).2 =
                  (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node 0)
                    (NamedRun.stateBefore S rho i 0).st
                    (NamedRun.stateBefore S rho i 0).record (n : Time)).2.2 :=
            ⟨_, rfl, rfl⟩
          rw [hstate, hgcState] at hu
          rcases Protocol.gfFrom_named_tick gc S.E S.hc S.cfg (S.node 0)
              (NamedRun.stateBefore S rho i 0).st
              (NamedRun.stateBefore S rho i 0).record (n : Time) k u hu with
            hold | hem | ⟨B, hB, hBu⟩
          · obtain ⟨j, hj, t, htick, hem⟩ := ih k u hold
            exact ⟨j, Nat.lt_succ_of_lt hj, t, htick, hem⟩
          · refine ⟨i, Nat.lt_succ_self i, n, he, ?_⟩
            exact ⟨i, he, by
              show NamedObject.gfVote u ∈
                (NamedNode.tick S 0 (NamedRun.stateBefore S rho i 0) (n : Time)).2
              rw [hgcEmit]
              exact hem⟩
          · have hBnode : NamedObject.block B ∈
                (NamedNode.tick S 0 (NamedRun.stateBefore S rho i 0) (n : Time)).2 := by
              rw [hgcEmit]
              exact hB
            obtain ⟨-, hproposal⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S 0
              (NamedRun.stateBefore S rho i 0) (n : Time) hBnode
            have hproposal' :
                Protocol.NamedActions.proposal_with
                    (NamedProfile.gradeContract
                      (NamedActionReads.confirmationReadFrom S
                        (NamedRun.stateBefore S rho i 0) (n : Time)).cache)
                    .poolAndCarried S.E S.hc (S.node 0)
                    (NamedActionReads.confirmationReadFrom S
                      (NamedRun.stateBefore S rho i 0) (n : Time)).st = some B := by
              unfold Protocol.NamedDuties.propose_block_with at hproposal
              cases hp : Protocol.NamedActions.proposal_with
                  (NamedProfile.gradeContract
                    (NamedActionReads.confirmationReadFrom S
                      (NamedRun.stateBefore S rho i 0) (n : Time)).cache)
                  .poolAndCarried S.E S.hc (S.node 0)
                  (NamedActionReads.confirmationReadFrom S
                    (NamedRun.stateBefore S rho i 0) (n : Time)).st with
              | none => rw [hp] at hproposal; simp at hproposal
              | some C => rw [hp] at hproposal; exact hproposal
            have hgf := Proofs.Optimistic.proposal_with_gf_votes
              (NamedProfile.gradeContract
                (NamedActionReads.confirmationReadFrom S
                  (NamedRun.stateBefore S rho i 0) (n : Time)).cache)
              .poolAndCarried S.E S.hc (S.node 0)
              (NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho i 0) (n : Time)).st hproposal'
            have huRead : u ∈
                (NamedActionReads.confirmationReadFrom S
                  (NamedRun.stateBefore S rho i 0) (n : Time)).st.core.gf_votes
                  ((NamedActionReads.confirmationReadFrom S
                    (NamedRun.stateBefore S rho i 0) (n : Time)).st.core.s - 1) := by
              rw [← hgf]
              exact hBu
            have huPre : u ∈
                (NamedRun.stateBefore S rho i 0).st.core.gf_votes
                  ((NamedActionReads.confirmationReadFrom S
                    (NamedRun.stateBefore S rho i 0) (n : Time)).st.core.s - 1) := by
              simpa only [NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using huRead
            have hstamps := Protocol.poolStamps_stateBefore S
              schedule_well_formed 0 i
            have hslot := hstamps.slot _ _ huPre
            have huPre' : u ∈
                (NamedRun.stateBefore S rho i 0).st.core.gf_votes u.slot := by
              rw [hslot]
              exact huPre
            obtain ⟨j, hj, t, htick, hem⟩ := ih u.slot u huPre'
            exact ⟨j, Nat.lt_succ_of_lt hj, t, htick, hem⟩

theorem emitted_block_gf_source {i : Nat} {B : NamedBlock (Fin 2)} {t : Time}
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i 0 t) :
    ∃ k : Slot, B.gf_votes =
      (NamedRun.stateBefore S rho i 0).st.core.gf_votes k := by
  obtain ⟨-, hproposal⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S rho i 0) t hB
  have hproposal' :
      Protocol.NamedActions.proposal_with
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho i 0) t).cache)
          .poolAndCarried S.E S.hc (S.node 0)
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hproposal
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st with
    | none => rw [hp] at hproposal; simp at hproposal
    | some C => rw [hp] at hproposal; exact hproposal
  have hgf := Proofs.Optimistic.proposal_with_gf_votes
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st hproposal'
  refine ⟨(NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st.core.s - 1, ?_⟩
  rw [hgf]
  rfl

theorem honest_gf_carried_origin {i : Nat} {B : NamedBlock (Fin 2)} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t))
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i 0 t)
    {u : GoldfishVote (Fin 2)} (hu : u ∈ B.gf_votes) :
    ∃ t' : Time, t' ≤ t ∧ NamedRun.emits S rho 0 (.gfVote u) t' := by
  obtain ⟨k, hsource⟩ := emitted_block_gf_source hB
  have huSource : u ∈
      (NamedRun.stateBefore S rho i 0).st.core.gf_votes k := by
    rw [← hsource]
    exact hu
  have hstamps := Protocol.poolStamps_stateBefore S
    schedule_well_formed 0 i
  have hslot : u.slot = k := hstamps.slot k u huSource
  have huSlot : u ∈
      (NamedRun.stateBefore S rho i 0).st.core.gf_votes u.slot := by
    rw [hslot]
    exact huSource
  obtain ⟨j, hj, t', htick, hem⟩ := honest_gf_pool_origin i u.slot u huSlot
  refine ⟨t', ?_, hem⟩
  have hmem : NamedEvent.tick (0 : Fin 2) t' ∈ rho.events.take i := by
    rw [List.mem_take_iff_getElem]
    obtain ⟨hjl, hget⟩ := List.getElem?_eq_some_iff.mp htick
    refine ⟨j, ?_, ?_⟩
    · rw [Nat.min_def]
      split <;> omega
    · change rho.events[j] = Event.tick 0 t'
      exact hget
  exact Execution.time_le_of_mem_take S schedule_well_formed hi
    _ hmem

theorem honest_row_origins :
    ∀ n : Nat,
      (∀ a : NamedAttestation (Fin 2), a.val_index ∈ rho.honest →
        a ∈ (NamedRun.stateBefore S rho n 0).st.sg_rows a.round →
        ∃ j, j < n ∧ ∃ t : Time,
          rho.events[j]? = some (.tick 0 t) ∧
            NamedRun.emits S rho 0 (.attest a) t) ∧
      (∀ B : NamedBlock (Fin 2),
        B ∈ (NamedRun.stateBefore S rho n 0).st.bodies →
        ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
        ∃ j, j < n ∧ ∃ t : Time,
          rho.events[j]? = some (.tick 0 t) ∧
            NamedRun.emits S rho 0 (.attest a) t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have emitted_block_row_origin :
          ∀ {m : Nat} {B : NamedBlock (Fin 2)} {t : Time}, m < n →
            rho.events[m]? = some (.tick 0 t) →
            NamedObject.block B ∈ NamedRun.emittedAt S rho m 0 t →
            ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
            ∃ j, j < m ∧ ∃ t' : Time,
              rho.events[j]? = some (.tick 0 t') ∧
                NamedRun.emits S rho 0 (.attest a) t' := by
        intro m B t hm hmtick hmem a ha hHon
        obtain ⟨-, hproposal⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S 0
          (NamedRun.stateBefore S rho m 0) t hmem
        let read := NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho m 0) t
        have hproposal' :
            Protocol.NamedActions.proposal_with
                (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
                (S.node 0) read.st = some B := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          cases hp : Protocol.NamedActions.proposal_with
              (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
              (S.node 0) read.st with
          | none => rw [hp] at hproposal; simp at hproposal
          | some C => rw [hp] at hproposal; exact hproposal
        have hpay := Proofs.NamedActions.proposal_payload
          (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
          (S.node 0) read.st B hproposal'
        have hrows : B.attestations =
            Protocol.NamedProposalRows.proposalRows B.parent
              (Protocol.NamedProposalRows.select .poolAndCarried S.hc read.st) :=
          hpay.2.2.2.2.2.2.1
        have haSelect : a ∈
            Protocol.NamedProposalRows.select .poolAndCarried S.hc read.st := by
          exact (Proofs.NamedProposalRows.mem_proposalRows B.parent _ a
            (hrows ▸ ha)).1
        simp only [Protocol.NamedProposalRows.select] at haSelect
        rcases List.mem_append.mp haSelect with haPool | haCarried
        · have haPool' := List.mem_filter.mp haPool
          obtain ⟨r, hr, haRow⟩ := List.mem_flatMap.mp haPool'.1
          have hrowPre : a ∈
              (NamedRun.stateBefore S rho m 0).st.sg_rows r := by
            simpa only [read, NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using haRow
          have hrounds := Proofs.NamedStoreBridge.sgRowRounds_stateBefore S rho m 0
          have haround : a.round = r := hrounds r a hrowPre
          have hrowOwn : a ∈
              (NamedRun.stateBefore S rho m 0).st.sg_rows a.round := by
            rw [haround]
            exact hrowPre
          obtain ⟨j, hj, t', htick, hem⟩ :=
            (ih m hm).1 a hHon hrowOwn
          exact ⟨j, hj, t', htick, hem⟩
        · obtain ⟨C, hC, heligible, haC, hwindow⟩ :=
            (Proofs.NamedProposalRows.mem_carried_rows S.hc read.st a).mp haCarried
          have hCbody : C ∈
              (NamedRun.stateBefore S rho m 0).st.bodies := by
            have := Proofs.NamedProposalRows.ordered_bodies_mem hC
            simpa only [read, NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using this
          obtain ⟨j, hj, t', htick, hem⟩ :=
            (ih m hm).2 C hCbody a haC hHon
          exact ⟨j, hj, t', htick, hem⟩
      constructor
      · intro a hHon ha
        obtain ⟨j, hj, t, hacc⟩ :=
          Proofs.NamedOutageProvenance.held_row_origin S rho n 0 ha
        obtain ⟨hactual, hpre, hpost⟩ := hacc
        rcases hactual with ⟨hindex, hevent⟩
        change NamedRun.actualHandlesAtIndex S rho j 0 (.attest a) at hindex
        rcases hindex with hdirect | ⟨B, q, before, hcarried⟩
        · change NamedRun.processesAtIndex S rho j 0 (.attest a) at hdirect
          rcases hdirect with ⟨te, he, hmem⟩ | ⟨td, he⟩
          · exact ⟨j, hj, te, he, ⟨j, he, hmem⟩⟩
          · obtain ⟨k, hk, hne⟩ := event_at_is_tick he
            cases hne
        · rcases hcarried with ⟨hcall, hnew, hheld, hindex⟩
          rcases hcall with hdeliver | ⟨te, he, hmem, hbefore⟩
          · rcases hdeliver with ⟨td, hdeliver, hbefore⟩
            obtain ⟨k, hk, hne⟩ := event_at_is_tick hdeliver
            cases hne
          · have haB : a ∈ B.attestations := List.mem_of_getElem? hindex
            obtain ⟨j', hj', t', htick', hem⟩ := emitted_block_row_origin
              hj he hmem a haB hHon
            exact ⟨j', Nat.lt_trans hj' hj, t', htick', hem⟩
      · intro B hB a ha hHon
        rcases Proofs.NamedOutageProvenance.held_block_origin S rho n 0 hB with
          hgen | ⟨j, hj, t, hacc⟩
        · subst B
          simp only [NamedBlock.attestations, List.not_mem_nil] at ha
        · obtain ⟨hactual, hpre, hpost⟩ := hacc
          rcases hactual with ⟨hindex, hevent⟩
          change NamedRun.actualHandlesAtIndex S rho j 0 (.block B) at hindex
          rcases hindex with ⟨te, he, hmem⟩ | ⟨td, he⟩
          · obtain ⟨j', hj', t', htick', hem⟩ := emitted_block_row_origin
                hj he hmem a ha hHon
            exact ⟨j', Nat.lt_trans hj' hj, t', htick', hem⟩
          · obtain ⟨k, hk, hne⟩ := event_at_is_tick
                he
            cases hne

theorem honest_attest_carried_origin {i : Nat} {B : NamedBlock (Fin 2)} {t : Time}
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i 0 t)
    {a : NamedAttestation (Fin 2)} (ha : a ∈ B.attestations)
    (haHon : a.val_index ∈ rho.honest) :
    ∃ j, j < i ∧ ∃ t' : Time,
      rho.events[j]? = some (.tick 0 t') ∧
        NamedRun.emits S rho 0 (.attest a) t' := by
  obtain ⟨-, hproposal⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S rho i 0) t hB
  let read := NamedActionReads.confirmationReadFrom S
    (NamedRun.stateBefore S rho i 0) t
  have hproposal' :
      Protocol.NamedActions.proposal_with
          (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
          (S.node 0) read.st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hproposal
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
        (S.node 0) read.st with
    | none => rw [hp] at hproposal; simp at hproposal
    | some C => rw [hp] at hproposal; exact hproposal
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract read.cache) .poolAndCarried S.E S.hc
    (S.node 0) read.st B hproposal'
  have hrows : B.attestations =
      Protocol.NamedProposalRows.proposalRows B.parent
        (Protocol.NamedProposalRows.select .poolAndCarried S.hc read.st) :=
    hpay.2.2.2.2.2.2.1
  have haSelect : a ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc read.st := by
    exact (Proofs.NamedProposalRows.mem_proposalRows B.parent _ a
      (hrows ▸ ha)).1
  simp only [Protocol.NamedProposalRows.select] at haSelect
  rcases List.mem_append.mp haSelect with haPool | haCarried
  · have haPool' := List.mem_filter.mp haPool
    obtain ⟨r, hr, haRow⟩ := List.mem_flatMap.mp haPool'.1
    have hrowPre : a ∈
        (NamedRun.stateBefore S rho i 0).st.sg_rows r := by
      simpa only [read, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using haRow
    have hrounds := Proofs.NamedStoreBridge.sgRowRounds_stateBefore S rho i 0
    have haround : a.round = r := hrounds r a hrowPre
    have hrowOwn : a ∈
        (NamedRun.stateBefore S rho i 0).st.sg_rows a.round := by
      rw [haround]
      exact hrowPre
    obtain ⟨j, hj, t', htick, hem⟩ :=
      (honest_row_origins i).1 a haHon hrowOwn
    exact ⟨j, hj, t', htick, hem⟩
  · obtain ⟨C, hC, heligible, haC, hwindow⟩ :=
      (Proofs.NamedProposalRows.mem_carried_rows S.hc read.st a).mp haCarried
    have hCbody : C ∈
        (NamedRun.stateBefore S rho i 0).st.bodies := by
      have := Proofs.NamedProposalRows.ordered_bodies_mem hC
      simpa only [read, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using this
    obtain ⟨j, hj, t', htick, hem⟩ :=
      (honest_row_origins i).2 C hCbody a haC haHon
    exact ⟨j, hj, t', htick, hem⟩

theorem authentic : Unforgeable S rho where
  unforgeable := by
    intro v o t hproc signer hsigner _hauthor
    have hsigner0 : signer = 0 := by
      change signer ∈ ({0} : Finset (Fin 2)) at hsigner
      simpa using hsigner
    rcases hproc with hemit | ⟨i, hdeliver⟩
    · have hv0 : v = 0 := emitted_node_zero hemit
      subst v
      subst signer
      exact ⟨t, le_rfl, hemit⟩
    · obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? hdeliver)
      cases hne
  carried_gf := by
    intro v B t hproc u huB huHon
    rcases hproc with hemit | ⟨i, hdeliver⟩
    · have hv0 : v = 0 := emitted_node_zero hemit
      subst v
      obtain ⟨i, hi, hmem⟩ := hemit
      have huv : u.val_index = 0 := by
        change u.val_index ∈ ({0} : Finset (Fin 2)) at huHon
        simpa using huHon
      rw [huv]
      exact honest_gf_carried_origin hi hmem huB
    · obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? hdeliver)
      cases hne
  carried_attest := by
    intro v B t hproc a haB haHon
    rcases hproc with hemit | ⟨i, hdeliver⟩
    · have hv0 : v = 0 := emitted_node_zero hemit
      subst v
      obtain ⟨i, hi, hmem⟩ := hemit
      have hav : a.val_index = 0 := by
        change a.val_index ∈ ({0} : Finset (Fin 2)) at haHon
        simpa using haHon
      obtain ⟨j, hj, t', htick, hem⟩ :=
        honest_attest_carried_origin hmem haB haHon
      rw [hav]
      exact ⟨t', by
        have hmemTake : NamedEvent.tick (0 : Fin 2) t' ∈ rho.events.take i := by
          rw [List.mem_take_iff_getElem]
          obtain ⟨hjl, hget⟩ := List.getElem?_eq_some_iff.mp htick
          refine ⟨j, ?_, ?_⟩
          · rw [Nat.min_def]
            split <;> omega
          · change rho.events[j] = Event.tick 0 t'
            exact hget
        exact Execution.time_le_of_mem_take S schedule_well_formed hi
          _ hmemTake, hem⟩
    · obtain ⟨n, hn, hne⟩ := event_mem_shape (List.mem_of_getElem? hdeliver)
      cases hne

theorem actual_handles_self {i : Nat} {o : NamedObject (Fin 2)} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t))
    (ho : o ∈ NamedRun.emittedAt S rho i 0 t) :
    NamedRun.actualHandlesAt S rho i 0 o t := by
  refine ⟨?_, ⟨.tick 0 t, hi, rfl, rfl⟩⟩
  cases o with
  | block B => exact Or.inl ⟨t, hi, ho⟩
  | gfVote u => exact Or.inl (Or.inl ⟨t, hi, ho⟩)
  | attest a => exact Or.inl (Or.inl ⟨t, hi, ho⟩)

theorem synchrony : Synchrony S rho where
  broadcast := by
    intro v hv o t hemit w hw hdeadline _hguard
    have hv0 : v = 0 := emitted_node_zero hemit
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    obtain ⟨i, hi, ho⟩ := hemit
    have hnonneg : 0 ≤ t := (schedule_in_horizon _
      (List.mem_of_getElem? hi)).1
    refine ⟨t, le_rfl, ?_, i, actual_handles_self hi ho⟩
    rw [show S.E.t_GST = 44 by rfl]
    exact lt_of_le_of_lt (le_max_left t 44)
      (lt_add_of_pos_right (max t 44) (by norm_num [S, E]))
  relay_block := by
    intro v hv i B t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss

  relay_gf_vote := by
    intro v hv i u t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss
  relay_attest := by
    intro v hv i a t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss

theorem stored_block_slot_le {i : Nat} {B : Block (Fin 2)}
    (hB : B ∈ (NamedRun.stateBefore S rho i 0).st.core.T) :
    B.slot ≤ (NamedRun.stateBefore S rho i 0).st.core.s := by
  obtain ⟨D, hD, hDErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho i 0 hB
  rcases Proofs.NamedOutageProvenance.held_block_origin S rho i 0 hD with
    hgen | ⟨j, hj, t, hacc⟩
  · subst D
    have hBgen : B = Block.genesis := by
      simpa only [NamedBlock.erase] using hDErase.symm
    subst B
    exact Nat.zero_le _
  · obtain ⟨hactual, hpre, hpost⟩ := hacc
    rcases hactual with ⟨hindex, hevent⟩
    change NamedRun.actualHandlesAtIndex S rho j 0 (.block D) at hindex
    rcases hindex with ⟨te, he, hmem⟩ | ⟨td, hdeliver⟩
    · have hshape := emitted_block_shape_local ⟨j, he, hmem⟩
      have hclock := Proofs.NamedRuntime.tick_time_le_clock S rho
        schedule_well_formed.sorted
        (fun e he' => (schedule_in_horizon e he').1) he hj
      have hproposal : Protocol.proposal_time S.E D.slot ≤
          (NamedRun.stateBefore S rho i 0).st.core.t := by
        rw [← hshape.2.1]
        exact hclock
      have hslot := Protocol.slot_le_slotOf_of_proposal_time_le
        S.E hproposal
      have hclockslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i 0
      unfold Proofs.Optimistic.SlotOfClock at hclockslot
      have hslotD : D.slot ≤
          (NamedRun.stateBefore S rho i 0).st.core.s := by
        rw [hclockslot]
        exact hslot
      have hslotErase : D.erase.slot ≤
          (NamedRun.stateBefore S rho i 0).st.core.s := by
        simpa only [Proofs.NamedWire.erase_slot] using hslotD
      simpa only [hDErase] using hslotErase
    · obtain ⟨k, hk, hne⟩ := event_at_is_tick hdeliver
      cases hne

theorem emitted_vote_head_block {i : Nat} {u : GoldfishVote (Fin 2)} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t))
    (hmem : NamedObject.gfVote u ∈ NamedRun.emittedAt S rho i 0 t) :
    ∃ H : NamedBlock (Fin 2),
      H ∈ (NamedRun.stateBefore S rho i 0).st.bodies ∧
      H.root = u.head ∧ H.slot ≤ u.slot := by
  have hshape := Proofs.Optimistic.gfVote_emitted_shape S 0
    (NamedRun.stateBefore S rho i 0) t hmem
  let read := NamedActionReads.confirmationReadFrom S
    (NamedRun.stateBefore S rho i 0) t
  have hpreInv := (Proofs.NamedRuntime.stateBefore_invariants S rho i 0).1
  have hreadInv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, NamedActionReads.confirmationReadFrom] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg
        (NamedRun.stateBefore S rho i 0).st t hpreInv
  have hroot : Protocol.get_fg_root read.st.core.toHealing.toFG ∈
      read.st.core.T := Proofs.NamedStoreRoots.fg_root_mem read.st hreadInv.1.2
  have hanchor : Protocol.get_sg_root_with
      (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
        (S.hc.round_of read.st.core.s) ∈ read.st.core.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s) hroot
  have htree :
      Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s ⊆
        read.st.core.T := by
    intro C hC
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      read.st.core.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore
        read.st.core.s) hC
    exact (Finset.mem_filter.mp hprocessed).1
  have hhead :
      Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1) ∈ read.st.core.T := by
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hheadPre :
      Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1) ∈
          (NamedRun.stateBefore S rho i 0).st.core.T := by
    simpa only [read, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hhead
  obtain ⟨H, hH, hHErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho i 0 hheadPre
  have hvote :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache) S.E S.hc (S.node 0) read.st).2 =
        some u := hshape.2.2.1
  have hrootHead : u.head =
      (Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1)).root := by
    have h := hvote
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at h
    split_ifs at h
    · exact Option.some.inj h |>.symm ▸ rfl
  have hHroot : H.root = u.head := by
    rw [← Proofs.NamedWire.erase_root H, hHErase]
    exact hrootHead.symm
  have hstored :
      (Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1)).slot ≤
        (NamedRun.stateBefore S rho i 0).st.core.s := by
    have := stored_block_slot_le (i := i)
      (B := Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1)) hheadPre
    exact this
  have hpreNonneg : 0 ≤
      (NamedRun.stateBefore S rho i 0).st.core.t :=
    Protocol.stateBefore_store_time_nonneg S schedule_well_formed 0 i
  have hpreClock :
      (NamedRun.stateBefore S rho i 0).st.core.t ≤ t := by
    exact Proofs.NamedRuntime.stateBefore_clock_le_event S rho
      schedule_well_formed.sorted hi (schedule_in_horizon _
        (List.mem_of_getElem? hi)).1 0
  have hpreSlot :
      (NamedRun.stateBefore S rho i 0).st.core.s ≤ S.E.slotOf t := by
    have hclockslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i 0
    unfold Proofs.Optimistic.SlotOfClock at hclockslot
    have hproposal := Protocol.proposal_time_slotOf_le S.E hpreNonneg
    rw [← hclockslot] at hproposal
    exact Protocol.slot_le_slotOf_of_proposal_time_le S.E
      (hproposal.trans hpreClock)
  have huSlot : u.slot = read.st.core.s := by
    exact hshape.2.2.2.2.trans (by
      simp only [read, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock])
  have hHslot : H.slot =
      (Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1)).slot := by
    have := congrArg Block.slot hHErase
    simpa only [Proofs.NamedWire.erase_slot] using this
  refine ⟨H, hH, hHroot, ?_⟩
  rw [hHslot]
  have hreadSlot : (NamedRun.stateBefore S rho i 0).st.core.s ≤ read.st.core.s := by
    simpa only [read, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hpreSlot
  have hreadToVote : read.st.core.s ≤ u.slot := by
    rw [← huSlot]
  exact hstored.trans (hreadSlot.trans hreadToVote)

theorem honest_committee_majority : Execution.HonestCommittees S rho.honest := by
  intro s
  norm_num [Execution.HonestCommittees, S, E, rho, Env.committee]

theorem total_weight_eq : S.E.W = 4 := by
  decide

theorem honest_weight_eq : S.E.electorate.weightOf rho.honest = 3 := by
  decide

theorem byzantine_weight_eq :
    S.E.electorate.weightOf (Finset.univ \ rho.honest) = 1 := by
  decide

theorem honest_awake : ∀ r : Round, (S.node 0).awake r = true := by
  intro r
  rfl

theorem byzantine_asleep : ∀ r : Round, (S.node 1).awake r = false := by
  intro r
  rfl

theorem awake_window_honest_mem (r : Round) (hr : 0 < r) :
    (0 : Fin 2) ∈ honestAwakeWindow (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r := by
  apply Finset.mem_filter.mpr
  refine ⟨by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨r - 1, ?_, ?_⟩
  · simp [Protocol.latest_window, S, hc, hr]
    omega
  · exact honest_awake (r - 1)

theorem awake_window_eq_honest (r : Round) (hr : 0 < r) :
    honestAwakeWindow (fun v => (S.node v).awake) rho.honest S.hc.η_SG r =
      ({0} : Finset (Fin 2)) := by
  ext v
  by_cases hv : v = 0
  · subst v
    constructor
    · intro _
      simp
    · intro _
      exact awake_window_honest_mem r hr
  · constructor
    · intro hmem
      exact Finset.mem_filter.mp hmem |>.1
    · intro hmem
      exact (hv (Finset.mem_singleton.mp hmem)).elim

theorem awake_window_majority : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r := by
  intro r hr hhor
  rw [AwakeWindowMajority, awake_window_eq_honest r hr]
  rw [byzantine_weight_eq]
  decide

theorem delivery_well_formed : NamedDeliveryWellFormed S rho where
  wire := delivery_wire
  deps := delivery_deps
  fresh := delivery_fresh

theorem execution_valid : ExecutionValid S rho := by
  exact
    { toNamedScheduleWellFormed := schedule_well_formed
      toNamedDeliveryWellFormed := delivery_well_formed
      toNamedRootCollisionFree := root_collision_free
      toNamedUnforgeable := authentic }

def b0 : Time := 43
def b1 : Time := 44
def stableRound : Round := 2

example :
    (Statements.Instantiation.constants S).outageStart (S.a stableRound) <
      (Statements.Instantiation.constants S).expiry (S.a stableRound) := by
  exact (Proofs.constants_valid S).outage_window_nonempty _

theorem round_le_three_of_twelve_mul_le {r : Round} (h : 12 * r ≤ 46) : r ≤ 3 := by
  by_contra hnot
  have hgt : 3 < r := Nat.lt_of_not_ge hnot
  have hmul : 12 * 4 ≤ 12 * r := Nat.mul_le_mul_left 12 hgt
  have hbad : 48 ≤ 46 := hmul.trans h
  norm_num at hbad

theorem honest_round_voters_stable :
    honestRoundVoters S rho stableRound = ({0} : Finset (Fin 2)) := by
  decide

theorem grade_forming_round_one : GradeFormingMajority S rho 1 := by
  unfold GradeFormingMajority
  decide

theorem grade_forming_round_two : GradeFormingMajority S rho 2 := by
  unfold GradeFormingMajority
  decide

theorem grade_forming_round_three : GradeFormingMajority S rho 3 := by
  unfold GradeFormingMajority
  decide

theorem covered_round_le_three {r : Round}
    (hcovered : RoundCovered S rho r) : r ≤ 3 := by
  rcases hcovered with haction | ⟨p, hp, hdomain⟩
  · norm_num [RoundCovered, Setup.a, Protocol.HealConfig.a,
      Protocol.HealConfig.opening_slot, Protocol.proposal_time, Env.t,
      slotStart, S, E, hc, cfg, rho] at haction
    ring_nf at haction
    have hNat : 6 + 12 * r ≤ 45 := by
      simpa [Nat.mul_comm] using (show 6 + r * 12 ≤ 45 by exact_mod_cast haction.2)
    apply round_le_three_of_twelve_mul_le
    exact (Nat.le_add_left (12 * r) 6).trans (hNat.trans (by norm_num))
  · cases p with
    | g0 =>
      norm_num [RoundCovered, DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
        Protocol.HealConfig.opening_slot, DecoupledConsensusModel.Protocol.Phase.domainOffset,
        Protocol.proposal_time, Env.t, slotStart, S, E, hc, cfg, rho] at hdomain
      ring_nf at hdomain
      have hNat : 1 + 12 * r ≤ 45 := by
        have hlt : r * 12 < 45 := by exact_mod_cast hdomain
        have hsucc : r * 12 + 1 ≤ 45 := Nat.succ_le_of_lt hlt
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsucc
      apply round_le_three_of_twelve_mul_le
      exact (Nat.le_add_left (12 * r) 1).trans (hNat.trans (by norm_num))
    | g1 =>
      norm_num [RoundCovered, DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
        Protocol.HealConfig.opening_slot, DecoupledConsensusModel.Protocol.Phase.domainOffset,
        Protocol.proposal_time, Env.t, slotStart, S, E, hc, cfg, rho] at hdomain
      ring_nf at hdomain
      have hNat : 12 * r ≤ 45 := by
        simpa [Nat.mul_comm] using (show r * 12 ≤ 45 by exact_mod_cast hdomain)
      apply round_le_three_of_twelve_mul_le
      exact hNat.trans (by norm_num)
    | g2 =>
      norm_num [RoundCovered, DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
        Protocol.HealConfig.opening_slot, DecoupledConsensusModel.Protocol.Phase.domainOffset,
        Protocol.proposal_time, Env.t, slotStart, S, E, hc, cfg, rho] at hdomain
      ring_nf at hdomain
      have hNat : 12 * r ≤ 46 := by
        simpa [Nat.mul_comm] using (show r * 12 ≤ 46 by exact_mod_cast hdomain)
      exact round_le_three_of_twelve_mul_le hNat

theorem previous_action_le_domain {r : Round} (hr : 0 < r)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    S.a (r - 1) ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r p := by
  cases p <;>
    norm_num [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
      DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening, Protocol.proposal_time,
      DecoupledConsensusModel.Protocol.Phase.domainOffset, Env.t, slotStart, S, E, hc, cfg]
  all_goals cases r with
  | zero => simp at hr ⊢
  | succ r =>
    simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
    ring_nf
    norm_num [DecoupledConsensusModel.Protocol.Phase.domainOffset]
    all_goals linarith

theorem outage_sleepy : OutageSleepyThroughout S rho := by
  intro r hr hcovered
  apply awake_window_majority r hr
  rcases hcovered with haction | ⟨p, hp, hdomain⟩
  · exact (by
      have := Proofs.Assembly.a_mono S (Nat.sub_le r 1)
      exact this.trans haction.2)
  · exact (previous_action_le_domain hr p).trans hdomain

theorem grade_forming : GradeFormingThroughout S rho := by
  intro r hr hcovered
  have hrle := covered_round_le_three hcovered
  interval_cases r
  · exact grade_forming_round_one
  · exact grade_forming_round_two
  · exact grade_forming_round_three

theorem awake_grade_majority_round_one : AwakeGradeMajority S rho 1 := by
  unfold AwakeGradeMajority
  decide

theorem awake_grade_majority_round_two : AwakeGradeMajority S rho 2 := by
  unfold AwakeGradeMajority
  decide

theorem awake_grade_majority_round_three : AwakeGradeMajority S rho 3 := by
  unfold AwakeGradeMajority
  decide

theorem awake_grade_majority : AwakeGradeMajorityThroughout S rho := by
  intro r hr hcovered
  have hrle := covered_round_le_three hcovered
  interval_cases r
  · exact awake_grade_majority_round_one
  · exact awake_grade_majority_round_two
  · exact awake_grade_majority_round_three

theorem formation_margin : FormationMargin S stableRound b0 := by
  norm_num [FormationMargin, stableRound, b0, Setup.a, Protocol.HealConfig.a,
    Protocol.HealConfig.opening_slot, Protocol.proposal_time, Env.t, slotStart,
    S, E, hc, cfg]

theorem retention_duration : RetentionDuration S rho stableRound b1 := by
  norm_num [RetentionDuration, stableRound, b1, Setup.a, Protocol.HealConfig.a,
    Protocol.HealConfig.opening_slot, Protocol.proposal_time, Env.t, slotStart,
    DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.opening,
    DecoupledConsensusModel.Protocol.Phase.earlyOffset, S, E, hc, cfg, rho]

theorem healthy_prefix : NamedHealthyPrefixDelivery S rho b0 where
  broadcast := by
    intro v hv o t hemit w hw hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    obtain ⟨i, hi, ho⟩ := hemit
    refine ⟨t, le_rfl, ?_, i, actual_handles_self hi ho⟩
    norm_num [S, E]
  relay_block := by
    intro v hv i B t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss
  relay_attest := by
    intro v hv i a t hacc w hw hmiss hdeadline _hguard
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    have hw0 : w = 0 := by
      change w ∈ ({0} : Finset (Fin 2)) at hw
      simpa using hw
    subst v
    subst w
    rw [hacc.2.2] at hmiss
    simp at hmiss

theorem outage_execution : OutageExecution S rho b0 b1 where
  execution := execution_valid
  synchrony := synchrony
  interval := by norm_num [b0, b1, rho]
  healthy := healthy_prefix
  gst := by norm_num [b1, S, E]
  boundaryPublic := by
    refine ⟨43, ?_⟩
    norm_num [b0, S, E]

theorem outage_regime :
    Statements.OutageRegime S (Statements.«instance» S)
      (Statements.ourConstants S) rho b0 b1 where
  execution := outage_execution.execution
  synchrony := outage_execution.synchrony
  gst := outage_execution.gst
  committees := by
    intro s
    exact honest_committee_majority s
  healthy := outage_execution.healthy
  interval := outage_execution.interval
  boundaryPublic := outage_execution.boundaryPublic
  participation := awake_grade_majority

theorem generic_outage_regime :
    Statements.Generic.OutageRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho (S.a stableRound) b0 b1 := by
  refine {
    execution := Proofs.genericExecutionValid_of_named S rho execution_valid
    partialSynchrony := Proofs.genericPartialSynchrony_of_named S rho synchrony
    gst := by simpa [Statements.Instantiation.env] using outage_execution.gst
    committees := ?_
    healthy := Proofs.genericHealthyPrefixDelivery_of_named S rho b0 healthy_prefix
    interval := outage_execution.interval
    boundaryPublic := by
      simpa [Statements.Instantiation.env, Statements.Generic.PublicTime,
        Execution.PublicTime] using outage_execution.boundaryPublic
    participation := ?_
    slashableBound := ?_
    window := ?_ }
  · intro s
    simpa [Statements.Instantiation.interface, Statements.instance] using
      honest_committee_majority s
  · intro t htlo hthi
    classical
    unfold Statements.Generic.FreshMajority
    have hL : 1 ≤ S.a 1 - S.a 0 := by
      exact Int.add_one_le_iff.mpr (Proofs.concretePeriod_pos S)
    have hat :
        Statements.Generic.awakeAt (Statements.Instantiation.env S) rho.honest
            (t - (Statements.Instantiation.constants S).participationLag) =
          ({0} : Finset (Fin 2)) := by
      rw [honest_eq]
      change ({0} : Finset (Fin 2)).filter (fun v =>
        (Statements.Instantiation.env S).awake v
          (t - (Statements.Instantiation.constants S).participationLag) = true) = {0}
      ext v
      by_cases hv : v = 0 <;> simp [hv, Statements.Instantiation.env, S, E, hc, node]
    have hin :
        Statements.Generic.awakeIn (Statements.Instantiation.env S) rho.honest
            (t - (Statements.Instantiation.constants S).participationWindow)
            (t - (Statements.Instantiation.constants S).participationLag) =
          ({0} : Finset (Fin 2)) := by
      rw [honest_eq]
      change ({0} : Finset (Fin 2)).filter (fun v =>
        ∃ u, t - (Statements.Instantiation.constants S).participationWindow ≤ u ∧
          u < t - (Statements.Instantiation.constants S).participationLag ∧
            (Statements.Instantiation.env S).awake v u = true) = {0}
      apply Finset.Subset.antisymm
      · intro v hv
        exact Finset.mem_singleton.mpr
          (by simpa using (Finset.mem_filter.mp hv).1)
      · intro v hv
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        apply Finset.mem_filter.mpr
        refine ⟨by simp, ⟨t - 13, ?_, ?_, ?_⟩⟩
        · change t - 24 ≤ t - 13
          linarith
        · norm_num [Statements.Instantiation.constants, S, E, hc,
            Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart]
        · rfl

    rw [hat, hin]
    simp [honest_eq, S, E, node, Statements.Instantiation.env,
      Electorate.weightOf]
    decide
  · intro c c' hc hc'
    have hbelow : BelowOneThird S rho.honest := by
      unfold BelowOneThird
      change 3 * S.E.electorate.weightOf
          (Finset.univ \ ({0} : Finset (Fin 2))) < S.E.W
      rw [total_weight_eq]
      have hweight : S.E.electorate.weightOf
          (Finset.univ \ ({0} : Finset (Fin 2))) = 1 := by decide
      rw [hweight]
      norm_num
    exact (Proofs.HealingSurface.slashableBound_of_admissibleCore_belowOneThird
      S (Proofs.AdmissibleCore.ofParts execution_valid synchrony) hbelow)
      c c' hc hc'
  · refine ⟨?_, ?_, ?_⟩
    · norm_num [Statements.Instantiation.constants, nextAction, roundAfter,
        roundLength, stableRound, b0, Setup.a, Protocol.HealConfig.a,
        Protocol.HealConfig.opening_slot, slotStart, S, E, hc, cfg]
    · norm_num [Statements.Instantiation.constants, nextAction, roundAfter,
        roundLength, stableRound, b1, Setup.a, Protocol.HealConfig.a,
        Protocol.HealConfig.opening_slot, slotStart, DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.opening, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        Protocol.proposal_time, Env.t, Env.slotOf, slotOfTime,
        Protocol.HealConfig.round_of, S, E, hc, cfg] <;> decide +kernel
    · norm_num [b1, rho, Statements.Instantiation.env, S, E]

def stableRead : NamedNodeState (Fin 2) :=
  roundConfirmationRead S rho 0 stableRound

noncomputable def stableCandidate : NamedBlock (Fin 2) :=
  Classical.choose (DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome S rho 1)

theorem stableCandidate_spec :
    Statements.Instantiation.proposedBlockAt S rho 1 = some stableCandidate := by
  exact Classical.choose_spec (DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome S rho 1)

def concreteStableCandidate : NamedBlock (Fin 2) :=
  .node .genesis 1 ⟨2⟩ [] [] [] 0

-- Kernel evaluation checks the complete finite proposal computation.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem proposed_block_concrete :
    Statements.Instantiation.proposedBlockAt S rho 1 = some concreteStableCandidate := by
  native_decide

theorem stableCandidate_eq_concrete : stableCandidate = concreteStableCandidate := by
  exact Option.some.inj (stableCandidate_spec.symm.trans proposed_block_concrete)

noncomputable def protectedBlock : Block (Fin 2) := stableCandidate.erase

theorem first_block_emits :
    NamedRun.emits S rho 0 (.block stableCandidate) 4 := by
  have h := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_emits_of_honest S
    schedule_well_formed 1 (by norm_num) (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp)
    (by norm_num [Protocol.proposal_time, Env.t, slotStart, S, E, rho])
  rcases h with ⟨B, hB, hslot, hem⟩
  have heq : B = stableCandidate :=
    Option.some.inj (hB.symm.trans stableCandidate_spec)
  subst B
  simpa [E] using hem

theorem stable_candidate_slot : stableCandidate.slot = 1 :=
  DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho 1 stableCandidate_spec

theorem stable_candidate_root : stableCandidate.root = ⟨2⟩ := by
  have hroot := emitted_block_root_local first_block_emits
  rw [hroot, stable_candidate_slot]

theorem stable_candidate_non_genesis : stableCandidate ≠ NamedBlock.genesis := by
  intro h
  have hone : stableCandidate.slot = 1 := stable_candidate_slot
  have hbad : (0 : Nat) = 1 := by
    rw [h] at hone
    change (0 : Nat) = 1 at hone
    exact hone
  exact Nat.noConfusion hbad

theorem protected_block_non_genesis : protectedBlock ≠ (Block.genesis : Block (Fin 2)) := by
  intro h
  have hslot : stableCandidate.slot = 0 := by
    have h' := congrArg Block.slot h
    simpa only [protectedBlock, Proofs.NamedWire.erase_slot] using h'
  have hone : stableCandidate.slot = 1 := stable_candidate_slot
  exact Nat.noConfusion (hslot.symm.trans hone)

-- Kernel evaluation checks the complete finite read computation.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem stable_at_concrete :
    stableAt S rho 0 stableRound protectedBlock := by
  rw [protectedBlock, stableCandidate_eq_concrete]
  refine ⟨concreteStableCandidate.erase, ?_, Block.preceq_self _⟩
  native_decide

theorem stable_tick_emission {i : Nat}
    (hi : rho.events[i]? = some (.tick 0 (S.a stableRound))) :
    NamedRun.emittedAt S rho i 0 (S.a stableRound) =
      [.attest (Proofs.HealingSurface.actionAttestationAt S rho 0 stableRound)] := by
  have h := Proofs.NamedActionSources.action_emission S rho schedule_well_formed
    i 0 stableRound hi
  simpa [node, stableRound] using h

theorem emitted_block_is_stable {B : NamedBlock (Fin 2)} {t : Time}
    (h : NamedRun.emits S rho 0 (.block B) t) : B = stableCandidate := by
  have hshape := emitted_block_shape_local h
  have hproposal := hshape.2.2
  change (if B.slot = 1 then 0 else 1) = 0 at hproposal
  have hslot : B.slot = 1 := by
    by_contra hne
    simp [hne] at hproposal
  exact Proofs.HealingSurface.emits_block_unique S schedule_well_formed h
    first_block_emits (by
      have hs := DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho 1 stableCandidate_spec
      simpa [hslot, hs])

theorem run_block_simple {B : NamedBlock (Fin 2)}
    (hB : NamedRun.blockInRun S rho B) :
    B = NamedBlock.genesis ∨ B = stableCandidate := by
  rcases run_block_origin hB with hgen | ⟨t, hem⟩
  · exact Or.inl hgen
  · exact Or.inr (emitted_block_is_stable hem)

theorem state_block_simple {t : Time} {B : Block (Fin 2)}
    (hB : B ∈ (NamedRun.stateBeforeTime S rho t 0).st.core.T) :
    B = Block.genesis ∨ B = stableCandidate.erase := by
  obtain ⟨D, hD, hDErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t 0 hB
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    schedule_well_formed.sorted t
  have hread0 := congrFun hread 0
  change D ∈ (NamedRun.stateBeforeTime S rho t 0).st.bodies at hD
  rw [hread0] at hD
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho
        (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp) n hD)
  rcases run_block_simple hDrun with hgen | hstable
  · left
    simpa [hgen] using hDErase.symm
  · right
    simpa [hstable] using hDErase.symm

theorem genesis_preceq : ∀ B : Block (Fin 2), Block.Preceq .genesis B := by
  intro B
  induction B with
  | genesis => exact Block.preceq_self _
  | node p slot root votes support rows proposer ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true]
      exact Or.inr ih

theorem body_retention_with_stamp {t u : Time} {B : NamedBlock (Fin 2)}
    (hB : B ∈ (NamedRun.stateBeforeTime S rho t 0).st.bodies)
    (htu : t ≤ u) :
    B ∈ (NamedRun.stateBeforeTime S rho u 0).st.bodies ∧
      (NamedRun.stateBeforeTime S rho u 0).st.core.timestamp_block B.erase =
        (NamedRun.stateBeforeTime S rho t 0).st.core.timestamp_block B.erase := by
  have hBt := hB
  rw [congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
    schedule_well_formed.sorted t) 0] at hBt
  rw [congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
    schedule_well_formed.sorted t) 0]
  rw [congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
    schedule_well_formed.sorted u) 0]
  exact Proofs.NamedBlockStamp.stateBefore_body_stamp_mono S rho 0
    (Proofs.NamedOutageClosure.strict_lengths_mono rho htu) hBt

theorem action_one_emits :
    NamedRun.emits S rho 0
      (.attest (Proofs.HealingSurface.actionAttestationAt S rho 0 1)) (S.a 1) := by
  exact Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake S
    schedule_well_formed (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp)
    1 (honest_awake 1) (by norm_num [Setup.a, Protocol.HealConfig.a,
      Protocol.HealConfig.opening_slot, Protocol.proposal_time, Env.t, slotStart,
      S, E, hc, cfg, rho])

theorem relative_carrier_window :
    Proofs.HealingSurface.RelativeCarrierWindowAt S rho 1
      DecoupledConsensusModel.Protocol.Phase.g2 := by
  intro w hw u hu
  have hw0 : w = 0 := by
    change w ∈ ({0} : Finset (Fin 2)) at hw
    simpa using hw
  have hu0 : u = 0 := by
    have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u 1).mp hu).1
    change u ∈ ({0} : Finset (Fin 2)) at huHon
    simpa using huHon
  subst w
  subst u
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.F
      S.hc.η_SG 2 (DecoupledConsensusModel.Protocol.early S.E S.hc 2 .g2) 0,
    y.round = 1 ∧
      y.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho 0 1).root ∧
        Block.find?
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.T
            (Proofs.HealingSurface.actionSGBlockAt S rho 0 1).root =
          some (Proofs.HealingSurface.actionSGBlockAt S rho 0 1)
  let a := Proofs.HealingSurface.actionAttestationAt S rho 0 1
  have haVal : a.val_index = 0 := by
    simpa [a] using (Proofs.HealingSurface.actionAttestationAt_shape S rho 0 1).1
  have haRound : a.round = 1 := by
    simpa [a] using (Proofs.HealingSurface.actionAttestationAt_shape S rho 0 1).2.1
  have haHon : a.val_index ∈ rho.honest := by
    rw [haVal]
    change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
    simp
  have hem : NamedRun.emits S rho 0 (.attest a) (S.a 1) := by
    simpa only [a] using action_one_emits
  have hem0 := hem
  obtain ⟨i, hi, hmem⟩ := hem
  have hcall : NamedRun.actualHandlesAt S rho i 0 (.attest a) (S.a 1) :=
    actual_handles_self hi hmem
  have hem' : NamedRun.emits S rho 0 (.attest a) (S.a a.round) := by
    simpa [haRound] using hem0
  have hcall' : NamedRun.actualHandlesAt S rho i 0 (.attest a) (S.a a.round) := by
    simpa [haRound] using hcall
  have hraw := Proofs.NamedOutageClosure.SGArrivalDeadline.outage_emitted_sg_raw_at_next_g2
    S rho b0 b1 outage_execution haHon hem' (by rfl) (by
      norm_num [haRound, Setup.a, Protocol.HealConfig.a,
        Protocol.HealConfig.opening_slot, DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.opening, Protocol.proposal_time, Env.t, slotStart,
        S, E, hc, cfg]) hcall'
  obtain ⟨i', hi', _, hhead⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_head S rho hem0
  dsimp at hhead
  obtain ⟨K, hKstaged, hKroot⟩ := hhead
  have hi1 : rho.events[i']? = some (.tick 0 (S.a 1)) := by
    simpa [a, haRound] using hi'
  have hstate := Proofs.NamedActionSources.action_read_index S rho
    schedule_well_formed i' 0 1 hi1
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a 1) 0).st.bodies := by
    rw [← hstate]
    simpa [NamedActionReads.actionReadFrom] using hKstaged
  have htime : S.a 1 ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2 := by
    norm_num [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
      DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening, DecoupledConsensusModel.Protocol.Phase.domainOffset,
      Protocol.proposal_time, Env.t, slotStart, S, E, hc, cfg]
  have hKsource' := hKsource
  rw [congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
    schedule_well_formed.sorted (S.a 1)) 0] at hKsource'
  have hKtarget : K ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.bodies :=
    by
      rw [congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
        schedule_well_formed.sorted
          (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2)) 0]
      exact Proofs.NamedBodyRetention.stateBefore_bodies_mono S rho 0
        (Proofs.NamedOutageClosure.strict_lengths_mono rho htime) hKsource'
  have hfind := Proofs.NamedOutageClosure.held_find_at_strict S rho
    schedule_well_formed execution_valid.toNamedRootCollisionFree 0
      (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) K hKtarget
  have hcompatible : Block.compatible K.erase
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.F = true := by
    have hKmem : K.erase ∈
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.T := by
      have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).1.1.1
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hKtarget
    have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0
    have hFs := state_block_simple hFmem
    have hKs := state_block_simple hKmem
    rcases hFs with hFgen | hFstable
    · rcases hKs with hKgen | hKstable
      · rw [hFgen, hKgen]
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (Block.preceq_self _)
      · rw [hFgen, hKstable]
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (genesis_preceq _)
    · rcases hKs with hKgen | hKstable
      · rw [hFstable, hKgen]
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (genesis_preceq _)
      · rw [hFstable, hKstable]
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (Block.preceq_self _)
  let H := Proofs.HealingSurface.actionSGBlockAt S rho 0 1
  have hHsourceCore : H ∈
      (NamedRun.stateBeforeTime S rho (S.a 1) 0).st.core.T := by
    simpa only [H] using
      (Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime S rho 0 1)
  obtain ⟨D, hDsource, hDErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a 1) 0 hHsourceCore
  have hDtarget := body_retention_with_stamp hDsource htime
  have hDprefix : D ∈
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < S.a 1))).length 0).st.bodies := by
    rw [← congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
      schedule_well_formed.sorted (S.a 1)) 0]
    exact hDsource
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho
        (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp) _ hDprefix)
  have hKprefix : K ∈
      (NamedRun.stateBefore S rho
        (rho.events.filter
          (fun e => decide (e.time < DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2))).length 0).st.bodies := by
    rw [← congrFun (Proofs.NamedOutageClosure.strict_read_eq_index S rho
      schedule_well_formed.sorted (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2)) 0]
    exact hKtarget
  have hKrun : NamedRun.blockInRun S rho K :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho
        (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp) _ hKprefix)
  have hAshape : a.confirmed = some H.root := by
    simpa [a, H] using
      (Proofs.HealingSurface.actionAttestationAt_shape S rho 0 1).2.2
  have hHKroot : H.root = K.root :=
    Option.some.inj (hAshape.symm.trans hKroot)
  have hDKroot : D.root = K.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = H.root := by rw [hDErase]
      _ = K.root := hHKroot
  have hDK : D = K :=
    execution_valid.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hHEq : H = K.erase := by
    calc
      H = D.erase := hDErase.symm
      _ = K.erase := congrArg NamedBlock.erase hDK
  have hfindH : Block.find?
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.T H.root = some H := by
    simpa [hHEq] using hfind
  refine ⟨Protocol.sgVote a.erase, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    unfold DecoupledConsensusModel.Protocol.bodyReady
    have hconfK : (Protocol.sgVote a.erase).confirmed = some K.erase.root := by
      rw [Proofs.NamedOutageClosure.sgVote_confirmed, hKroot,
        Proofs.NamedWire.erase_root]
    have hfindK : Block.find?
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.toHealing.gradeView.T
        K.erase.root = some K.erase := by
      simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hfind
    rw [hconfK]
    simp only
    rw [hfindK]
    simp only
    have hKsourceEarly := body_retention_with_stamp (B := K) (t := S.a 1)
      (u := DecoupledConsensusModel.Protocol.early S.E S.hc 2 .g2) hKsource (by
      norm_num [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
        DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.opening, Protocol.proposal_time,
        Env.t, slotStart, S, E, hc, cfg])
    have hstampEarly := Proofs.NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
      S rho schedule_well_formed 0
      (DecoupledConsensusModel.Protocol.early S.E S.hc 2 .g2) K hKsourceEarly.1
    have hKsourceTarget := body_retention_with_stamp (B := K) (t := S.a 1)
      (u := DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) hKsource htime
    have hstamp : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc 2 .g2) 0).st.core.timestamp_block
        (DecoupledConsensusModel.Protocol.early S.E S.hc 2 .g2) K.erase = true := by
      have hstampEq := hKsourceTarget.2.trans hKsourceEarly.2.symm
      unfold stampedBefore at hstampEarly ⊢
      rw [hstampEq]
      exact hstampEarly
    rw [Bool.and_eq_true]
    exact ⟨hstamp, hcompatible⟩
  · have hconfH : (Protocol.sgVote a.erase).confirmed = some H.root := by
      rw [Proofs.NamedOutageClosure.sgVote_confirmed]
      exact hAshape
    exact ⟨haRound, hconfH, hfindH⟩

theorem below_one_third : BelowOneThird S rho.honest := by
  unfold BelowOneThird
  change 3 * S.E.electorate.weightOf
      (Finset.univ \ ({0} : Finset (Fin 2))) < S.E.W
  rw [total_weight_eq]
  have hweight : S.E.electorate.weightOf
      (Finset.univ \ ({0} : Finset (Fin 2))) = 1 := by decide
  rw [hweight]
  norm_num

theorem slashable_bound : Internal.NamedOutageEntry.SlashableBound S rho := by
  exact Proofs.HealingSurface.slashableBound_of_admissibleCore_belowOneThird
    S (Proofs.AdmissibleCore.ofParts execution_valid synchrony) below_one_third

-- Kernel evaluation checks the complete finite stable-output read at the
-- round-2 action.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem stable_output_concrete :
    Block.Preceq protectedBlock
      (Protocol.get_stable (Run.storeAt S rho 0 (S.a stableRound)).core) := by
  rw [protectedBlock, stableCandidate_eq_concrete]
  native_decide

theorem outage_time_margin :
    nextAction S (S.a stableRound) + roundLength S + S.E.Δ ≤ b0 := by
  norm_num [nextAction, roundAfter, roundLength, stableRound, b0, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart, S, E, hc, cfg]

theorem outage_time_retention :
    b1 + S.E.Δ ≤ nextAction S (S.a stableRound) +
      ((S.hc.η_SG : Time) + 1) * roundLength S - 11 * S.E.Δ := by
  norm_num [nextAction, roundAfter, roundLength, stableRound, b1, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart, S, E, hc, cfg]

theorem asynchrony_resilience_activated :
    ∀ w ∈ rho.honest, ∀ t, b0 ≤ t → t ≤ rho.horizon →
      Block.Preceq protectedBlock
        (Protocol.get_stable (NamedRun.readAt S rho t w).st.core) := by
  have houtput :
      Block.Preceq protectedBlock
        (readAt S rho (Statements.«instance» S).stable 0 (S.a stableRound)) := by
    change Block.Preceq protectedBlock
      (Protocol.get_stable (Run.storeAt S rho 0 (S.a stableRound)).core)
    exact stable_output_concrete
  have hmargin :
      nextAction S (S.a stableRound) +
          (Statements.ourConstants S).formationMargin ≤ b0 := by
    norm_num [Statements.ourConstants, nextAction, roundAfter, roundLength,
      stableRound, b0, Setup.a, Protocol.HealConfig.a,
      Protocol.HealConfig.opening_slot, slotStart, S, E, hc, cfg]
  have hexpiry :
      b1 + S.E.Δ ≤ (Statements.ourConstants S).expiry
        (nextAction S (S.a stableRound)) := by
    norm_num [Statements.ourConstants, nextAction, roundAfter, roundLength,
      stableRound, b1, Setup.a, Protocol.HealConfig.a,
      Protocol.HealConfig.opening_slot, slotStart, DecoupledConsensusModel.Protocol.early,
      DecoupledConsensusModel.Protocol.opening, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      Protocol.proposal_time, Env.t, Env.slotOf, slotOfTime,
      Protocol.HealConfig.round_of, S, E, hc, cfg] <;> decide +kernel
  have hpre : Block.Preceq protectedBlock
      (Generic.readAt (DecoupledConsensusModel.Execution.spec S) rho
        (fun n => Protocol.get_stable n.st.core) 0 (S.a stableRound)) := by
    rw [Proofs.readAt_eq S rho (fun st => Protocol.get_stable st) 0
      (S.a stableRound)]
    exact houtput
  have h := (Proofs.concreteConsensus S).stablePersists
    rho (S.a stableRound) b0 b1 generic_outage_regime
  have hIn := h 0
    (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp)
    protectedBlock hpre
  intro w hw t ht htime
  have hProps := (Proofs.inBy_iff S rho (fun st => Protocol.get_stable st)
    protectedBlock t).mp (hIn t ht htime)
  exact hProps w hw

#print axioms asynchrony_resilience_activated

set_option maxHeartbeats 4000000 in
theorem leak_fairness_witness :
    Internal.LeakFairness.LeakFairnessExecution S rho ∧
      Internal.NamedOutageEntry.SlashableBound S rho ∧
      (0 : Fin 2) ∈ rho.honest ∧
      Internal.LeakFairness.currentProductionSource S rho 0 1 =
        some concreteStableCandidate.erase ∧
      Internal.LeakFairness.CurrentProductionSourceAtFrontier S rho 0 1
        concreteStableCandidate.erase := by
  refine ⟨⟨schedule_well_formed.sorted, schedule_well_formed.nodup,
      root_collision_free⟩, slashable_bound,
    (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp), ?_, ?_⟩
  · native_decide
  · unfold Internal.LeakFairness.CurrentProductionSourceAtFrontier
    native_decide

set_option maxHeartbeats 4000000 in
theorem leak_fairness_activated :
    Internal.LeakFairness.CurrentProductionHeightContribution S rho 0 1
        concreteStableCandidate.erase ∧
      Internal.LeakFairness.CurrentProductionL1Protection S rho 0 1
        concreteStableCandidate.erase := by
  rcases leak_fairness_witness with ⟨hcore, hsb, hv, hsource, hfrontier⟩
  exact Proofs.leakFairness S rho 0 1 concreteStableCandidate.erase
    hcore hsb hv hsource hfrontier

#print axioms leak_fairness_witness
#print axioms leak_fairness_activated

/-! The finite witness certifies the complete execution, timing, stable-read,
fresh-support and public-output bundle. -/

theorem outage_witness_core :
    OutageExecution S rho b0 b1 ∧
      Internal.NamedOutageEntry.SlashableBound S rho ∧
      HonestCommittees S rho.honest ∧
      AwakeGradeMajorityThroughout S rho ∧
      (0 : Fin 2) ∈ rho.honest ∧
      FormationMargin S stableRound b0 ∧
      RetentionDuration S rho stableRound b1 := by
  exact ⟨outage_execution, slashable_bound, honest_committee_majority,
    awake_grade_majority,
    (by change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)); simp),
    formation_margin, retention_duration⟩

#print axioms outage_witness_core


/-! ## End of the reusable finite-run core -/

end Outage
end Witnesses
end DecoupledConsensusModel

end
