module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ReviewTheorem

@[expose] public section

/-!
# Weak-participation GST-zero witness

This file starts the concrete `Fin 2` run used for the weak-genesis branches. The
single honest validator is `0`; validator `1` is Byzantine and is silent.
The run ticks the honest validator at every public time through time `30`.
-/



namespace DecoupledConsensusModel
namespace Witnesses

open Internal Execution Statements

def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => {0}⟩
  electorate :=
    { weight := fun v => if v = 0 then 2 else 1
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
  (List.range 31).map (fun n => .tick 0 (n : Time))

def rho : Run (Fin 2) :=
  { honest := {0}
    horizon := 30
    events := events }

theorem gst_zero : S.E.t_GST = 0 := rfl

theorem horizon_eq : rho.horizon = 30 := rfl

/-!
The executable run has 31 ticks, at times `0` through `30`. Its nonempty
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
    ∃ n : Nat, n < 31 ∧ e = .tick 0 (n : Time) := by
  change e ∈ (List.range 31).map (fun n : Nat => .tick 0 (n : Time)) at he
  obtain ⟨n, hn, hne⟩ := List.mem_map.mp he
  exact ⟨n, by simpa using hn, hne.symm⟩

theorem schedule_sorted : rho.events.Pairwise
    (fun e f => NamedEvent.key e ≤ NamedEvent.key f) := by
  change ((List.range 31).map
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
  refine (hrange 31).imp ?_
  intro n m hnm
  rcases Nat.lt_or_eq_of_le hnm with hlt | rfl
  · simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase,
      Prod.Lex.toLex_le_toLex, hlt]
  · simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase]

theorem schedule_nodup : rho.events.Nodup := by
  change ((List.range 31).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time))).Nodup
  apply (List.nodup_range : (List.range 31).Nodup).map
  intro n m h
  have hnm : (n : Time) = (m : Time) := congrArg NamedEvent.time h
  exact_mod_cast hnm

theorem schedule_in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := event_mem_shape he
  change 0 ≤ (n : Time) ∧ (n : Time) ≤ (30 : Time)
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
  have hn31 : n < 31 := by
    rw [hnt] at hhor
    change (n : Time) ≤ 30 at hhor
    have hn30 : n ≤ 30 := by exact_mod_cast hhor
    omega
  rw [hnt]
  exact List.mem_map.mpr ⟨n, by simpa using hn31, rfl⟩

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
  change ((List.range 31).map
      (fun n : Nat => NamedEvent.tick (0 : Fin 2) (n : Time))).filterMap
      NamedEvent.object? = []
  simp [NamedEvent.object?]

theorem event_at_is_tick {i : Nat} {e : Event (Fin 2)}
    (he : rho.events[i]? = some e) : ∃ n : Nat, n < 31 ∧ e = .tick 0 (n : Time) := by
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
  change ((List.range 31).map
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
    rw [show S.E.t_GST = 0 by rfl, max_eq_left hnonneg]
    exact lt_add_of_pos_right t (by norm_num [S, E])
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

theorem total_weight_eq : S.E.W = 3 := by
  decide

theorem honest_weight_eq : S.E.electorate.weightOf rho.honest = 2 := by
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
  · exact Protocol.pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr
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

theorem proposer_opening_carrier_recurrence :
    ProposerOpeningCarrierRecurrence S rho 2 := by
  intro k _ _
  refine ⟨k + 2, le_rfl, le_rfl, ?_⟩
  simp [ProposerOpeningCarrierAt, ProposerCarrierAt, S, E, hc, rho]

theorem admissible_core : AdmissibleCore S rho := by
  exact
    { toNamedScheduleWellFormed := schedule_well_formed
      toNamedDeliveryWellFormed := delivery_well_formed
      toNamedRootCollisionFree := root_collision_free
      toNamedUnforgeable := authentic }

theorem weak_genesis : Statements.WeakGenesis S rho where
  execution := admissible_core
  synchrony := synchrony
  committees := honest_committee_majority
  gstZero := gst_zero
  windows := awake_window_majority

theorem generic_sleepy_regime :
    Statements.Generic.SleepyRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 := by
  refine {
    execution := Proofs.genericExecutionValid_of_named S rho admissible_core
    partialSynchrony := Proofs.genericPartialSynchrony_of_named S rho synchrony
    gst := by simpa [Statements.Instantiation.env] using gst_zero.le
    committees := ?_
    windows := ?_
    start := Statements.Generic.RecoveredBy.genesis }
  · intro s
    simpa [Statements.Instantiation.interface, Statements.instance] using
      honest_committee_majority s
  · intro t ht hlag hhor
    classical
    have hL : 1 ≤ S.a 1 - S.a 0 := by
      have hpos := Proofs.concretePeriod_pos S
      exact Int.add_one_le_iff.mpr hpos
    have hawake :
        Statements.Generic.awakeIn (Statements.Instantiation.env S) rho.honest
            (t - (Statements.Instantiation.constants S).participationWindow) t =
          ({0} : Finset (Fin 2)) := by
      rw [honest_eq]
      change ({0} : Finset (Fin 2)).filter (fun v =>
        ∃ u, t - (Statements.Instantiation.constants S).participationWindow ≤ u ∧
          u < t ∧ (Statements.Instantiation.env S).awake v u = true) = {0}
      apply Finset.Subset.antisymm
      · intro v hv
        exact Finset.mem_singleton.mpr
          (by simpa using (Finset.mem_filter.mp hv).1)
      · intro v hv
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        apply Finset.mem_filter.mpr
        refine ⟨by simp, ⟨t - 1, ?_, sub_lt_self _ (by norm_num), ?_⟩⟩
        · simp [Statements.Instantiation.constants, hc]
          have heta : (0 : Time) < S.hc.η_SG := by
            exact_mod_cast Nat.zero_lt_of_lt S.hc.η_SG_ge_one
          exact mul_pos heta (Proofs.concretePeriod_pos S)
        · rfl
    unfold Statements.Generic.WindowMajority
    rw [hawake]
    change S.E.electorate.weightOf (Finset.univ \ rho.honest) <
      S.E.electorate.weightOf ({0} : Finset (Fin 2))
    rw [byzantine_weight_eq, ← honest_eq, honest_weight_eq]
    norm_num

theorem generic_fresh_sleepy_regime :
    Statements.Generic.FreshSleepyRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 := by
  refine { toSleepyRegime := generic_sleepy_regime, fresh := ?_ }
  intro t _ht _hlag _hhor
  classical
  unfold Statements.Generic.FreshMajority
  have hat :
      Statements.Generic.awakeAt (Statements.Instantiation.env S) rho.honest
          (t - (Statements.Instantiation.constants S).participationLag) =
        ({0} : Finset (Fin 2)) := by
    rw [honest_eq]
    change ({0} : Finset (Fin 2)).filter (fun v =>
      (Statements.Instantiation.env S).awake v
        (t - (Statements.Instantiation.constants S).participationLag) = true) = {0}
    ext v
    by_cases hv : v = 0 <;> simp [hv, Statements.Instantiation.env, S, node]
  have hstale :
      Statements.Generic.awakeIn (Statements.Instantiation.env S) rho.honest
          (t - (Statements.Instantiation.constants S).participationWindow)
          (t - (Statements.Instantiation.constants S).participationLag) \
        Statements.Generic.awakeAt (Statements.Instantiation.env S) rho.honest
          (t - (Statements.Instantiation.constants S).participationLag) = ∅ := by
    rw [hat]
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    rcases Finset.mem_sdiff.mp hv with ⟨hin, hnot⟩
    have hvH : v ∈ rho.honest := (Finset.mem_filter.mp hin).1
    rw [honest_eq] at hvH
    exact hnot hvH
  rw [hstale, Finset.union_empty, hat]
  change S.E.electorate.weightOf (Finset.univ \ rho.honest) <
    S.E.electorate.weightOf ({0} : Finset (Fin 2))
  rw [byzantine_weight_eq, ← honest_eq, honest_weight_eq]
  norm_num

theorem genesis_growth_guard_active :
    ∃ t : Time, t + (Statements.Instantiation.constants S).growthDelay 2 ≤
      rho.horizon := by
  refine ⟨0, ?_⟩
  norm_num [Statements.Instantiation.constants, S, E, hc, cfg, rho,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart]

theorem genesis_inclusion_guard_active :
    ∃ s, (Statements.Instantiation.interface S).proposalTime s +
      (Statements.Instantiation.constants S).confirmationDelay ≤ rho.horizon := by
  refine ⟨1, ?_⟩
  norm_num [Statements.Instantiation.interface, Statements.Instantiation.constants,
    S, E, hc, cfg, rho, Protocol.proposal_time, Env.t, slotStart]

/-! ## Closed theorem applications -/

theorem gst_zero_guarantees_activated : GSTZeroGuarantees S rho :=
  Proofs.gstZeroGuarantees S rho weak_genesis

theorem honest_proposal_confirmation_activated :
    HonestProposalsConfirmedFrom S rho 0 :=
  (Proofs.honestProposalConfirmation S).gstZero rho weak_genesis

theorem proposer_recurrence_activated :
    ProposerOpeningCarrierRecurrence S rho 2 :=
  proposer_opening_carrier_recurrence

theorem available_chain_growth_activated :
    AvailableChainGrowthFrom S rho 0 2 :=
  (Proofs.availableChainGrowth S).gstZero rho weak_genesis 2
    proposer_recurrence_activated

theorem stable_record_growth_activated :
    StableRecordGrowthFrom S rho 0 (2 + S.hc.η_SG - 1) :=
  (Proofs.stableRecordGrowth S).gstZero rho weak_genesis 2
    proposer_recurrence_activated

theorem finalized_prefix_activated : FinalizedPrefixConfirmed S rho :=
  Proofs.finalizedPrefix S rho

theorem nested_outputs_activated : Internal.NestedOutputs S :=
  Proofs.nestedOutputs S

theorem nested_outputs_activated_on_run (v : Fin 2) (t : Time) :
    let st := (NamedRun.readAt S rho t v).st.core
    Block.Preceq st.F (Protocol.get_stable st) ∧
      Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st) := by
  exact (Proofs.nestedOutputs S) rho v t

theorem liveness_activated : Statements.Liveness S :=
  Proofs.liveness S

theorem attestation_authenticity : AttestationAuthenticity S rho :=
  ⟨NamedUnforgeable.carried_attest authentic⟩

theorem vote_safety_schedule : VoteSafetySchedule S rho :=
  { sorted := schedule_well_formed.sorted
    honest_only := schedule_well_formed.honest_only }

theorem emission_vote_safety_activated :
    ∀ (v : Fin 2) (a b : NamedAttestation (Fin 2)),
      (∃ ta : Time, rho.emits S v (.attest a) ta) →
      (∃ tb : Time, rho.emits S v (.attest b) tb) →
      ¬ Protocol.Slashable a.erase b.erase :=
  (Proofs.voteSafetyOfClients S).emission rho vote_safety_schedule

theorem attributed_vote_safety_activated :
    ∀ u v t t' i, i ∈ rho.honest →
      ¬ SlashableBetween
        (store_attestations (rho.storeAt S u t).core)
        (store_attestations (rho.storeAt S v t').core) i :=
  (Proofs.voteSafetyOfClients S).attributed rho vote_safety_schedule
    attestation_authenticity

theorem vote_safety_of_clients_activated :
    (∀ (v : Fin 2) (a b : NamedAttestation (Fin 2)),
      (∃ ta : Time, rho.emits S v (.attest a) ta) →
      (∃ tb : Time, rho.emits S v (.attest b) tb) →
      ¬ Protocol.Slashable a.erase b.erase) ∧
    (∀ u v t t' i, i ∈ rho.honest →
      ¬ SlashableBetween
        (store_attestations (rho.storeAt S u t).core)
        (store_attestations (rho.storeAt S v t').core) i) :=
  ⟨emission_vote_safety_activated, attributed_vote_safety_activated⟩

theorem round_zero_growth_is_covered : S.a (0 + 2) ≤ rho.horizon := by
  norm_num [S, E, hc, rho, Protocol.HealConfig.a,
    Protocol.HealConfig.opening_slot, slotStart]

#print axioms gst_zero_guarantees_activated
#print axioms honest_proposal_confirmation_activated
#print axioms proposer_recurrence_activated
#print axioms available_chain_growth_activated
#print axioms stable_record_growth_activated
#print axioms finalized_prefix_activated
#print axioms nested_outputs_activated
#print axioms nested_outputs_activated_on_run
#print axioms liveness_activated
#print axioms attestation_authenticity
#print axioms emission_vote_safety_activated
#print axioms attributed_vote_safety_activated
#print axioms vote_safety_of_clients_activated
#print axioms genesis_growth_guard_active
#print axioms genesis_inclusion_guard_active

end Witnesses
end DecoupledConsensusModel

end
