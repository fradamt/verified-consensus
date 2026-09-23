module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel
public import DecoupledConsensusProofs.ReviewTheorem
public import DecoupledConsensusInternal.Legacy.Definitions.FinalityDeadlinesInternal
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Witnesses.FinalityLiveness

open Internal Execution Statements

/-! This file is the concrete GST-zero finality-liveness witness. The run has
one honest validator, one silent Byzantine validator, and a public tick at
every integer time in its finite horizon. The definitions below are kept
small while the execution proofs are developed from named primitive facts. -/

def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => {0}⟩
  electorate :=
    { weight := fun v => if v = 0 then 3 else 1
      weight_pos := by
        intro v
        fin_cases v <;> simp }

def hc : Protocol.HealConfig where
  R := 3
  R_ge_three := by norm_num
  η_SG := 2
  η_SG_ge_one := by norm_num

def cfg : Protocol.HeightConfig where
  K := 5
  D := 2
  timeoutDelay := 6
  K_ge_four := by norm_num
  D_ge_two := by norm_num

def node (v : Fin 2) : Protocol.Node (Fin 2) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => v = 0

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

def gap : Round := 3
def extra : Nat := 0

def startup : Round :=
  Statements.Instantiation.finalityStartup S gap extra

def phase : Round :=
  Proofs.HealingSurface.recurringFinalityPhaseLag
    (Proofs.HealingSurface.progressLag' gap extra) gap

def deadline : Round :=
  Statements.Instantiation.finalityDeadline S gap extra

def horizon : Time := 33729

theorem startup_value : startup = 654 := by
  norm_num [startup, Statements.Instantiation.finalityStartup, gap, extra, S, E, hc, cfg]

theorem phase_value : phase = 191 := by
  norm_num [phase, gap, extra, Proofs.HealingSurface.progressLag',
    Proofs.HealingSurface.seedLag,
    Proofs.HealingSurface.recurringFinalityPhaseLag,
    Proofs.HealingSurface.recurringFinalitySelectionLag,
    Proofs.HealingSurface.recurringFinalityPhaseCount, S, E, hc, cfg]

theorem deadline_value : deadline = 2151 := by
  norm_num [deadline, Statements.Instantiation.finalityDeadline, gap, extra, S, E, hc, cfg]

theorem horizon_formula :
    (Statements.Instantiation.constants S).finalityStartup gap +
        (gap : Time) * (Statements.Instantiation.constants S).period +
        (Statements.Instantiation.constants S).finalityDeadline gap = horizon := by
  norm_num [horizon, Statements.Instantiation.constants,
    Statements.Instantiation.finalityStartup, Statements.Instantiation.finalityDeadline,
    Setup.extraRounds,
    gap, extra, S, E, hc, cfg, Setup.a, Protocol.HealConfig.a,
    Protocol.HealConfig.opening_slot, healingBoundaryTime,
    Protocol.vote_time, Env.t, slotStart]

def eventCount : Nat := Int.toNat horizon

def tickEvents : Nat → Nat → List (Event (Fin 2))
  | _, 0 => []
  | k, n + 1 => .tick 0 (k : Time) :: tickEvents (k + 1) n

def events : List (Event (Fin 2)) :=
  tickEvents 0 (eventCount + 1)

def rho : Run (Fin 2) :=
  { honest := {0}
    horizon := horizon
    events := events }

set_option maxRecDepth 100000

theorem tickEvents_mem (start count : Nat) :
    ∀ e ∈ tickEvents start count,
      ∃ n : Nat, start ≤ n ∧ n < start + count ∧
        e = .tick 0 (n : Time) := by
  induction count generalizing start with
  | zero =>
      intro e he
      simp [tickEvents] at he
  | succ count ih =>
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨start, le_rfl, by omega, rfl⟩
      · obtain ⟨n, hstart, hlt, hshape⟩ := ih (start + 1) e he
        exact ⟨n, by omega, by omega, hshape⟩

theorem tickEvents_mem_of_time (start count n : Nat)
    (hstart : start ≤ n) (hlt : n < start + count) :
    .tick 0 (n : Time) ∈ tickEvents start count := by
  induction count generalizing start n with
  | zero => omega
  | succ count ih =>
      simp only [tickEvents, List.mem_cons]
      by_cases hsame : n = start
      · subst n
        simp
      · right
        apply ih (start + 1) n
        · omega
        · omega

theorem tickEvents_pairwise (start count : Nat) :
    (tickEvents start count).Pairwise
      (fun e f => NamedEvent.key e ≤ NamedEvent.key f) := by
  induction count generalizing start with
  | zero => exact List.Pairwise.nil
  | succ count ih =>
      simp only [tickEvents, List.pairwise_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro e he
      obtain ⟨n, hstart, hlt, hshape⟩ := tickEvents_mem (start + 1) count e he
      rw [hshape]
      simp only [NamedEvent.key, NamedEvent.time, NamedEvent.phase,
        Prod.Lex.toLex_le_toLex]
      left
      exact_mod_cast (Nat.lt_of_succ_le hstart)

theorem tickEvents_nodup (start count : Nat) :
    (tickEvents start count).Nodup := by
  induction count generalizing start with
  | zero => exact List.nodup_nil
  | succ count ih =>
      simp only [tickEvents, List.nodup_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro he
      obtain ⟨n, hstart, hlt, hshape⟩ := tickEvents_mem (start + 1) count _ he
      have htime : (start : Time) = (n : Time) :=
        congrArg NamedEvent.time hshape
      have hnat : start = n := by exact_mod_cast htime
      omega

/- These diagnostic evaluations run in plain Lean scripts, not in a module:
#eval startup
#eval phase
#eval deadline
#eval horizon
#eval events.length
#eval (NamedRun.emittedAt S rho 4 0 4).map (fun o => match o with
  | .block B => ("block", B.slot, B.root.value, B.gf_votes.length, B.attestations.length)
  | .gfVote u => ("vote", u.slot, u.head.value, 0, 0)
  | .attest a => ("attest", a.round, (a.confirmed.map BlockId.value).getD 0, 0, 0))
#eval (NamedRun.emittedAt S rho 5 0 5).map (fun o => match o with
  | .block B => ("block", B.slot, B.root.value, B.gf_votes.length, B.attestations.length)
  | .gfVote u => ("vote", u.slot, u.head.value, 0, 0)
  | .attest a => ("attest", a.round, (a.confirmed.map BlockId.value).getD 0, 0, 0))
-/

/-! ## Run and schedule primitives -/

theorem honest_eq : rho.honest = ({0} : Finset (Fin 2)) := rfl

theorem honest_nonempty : rho.honest.Nonempty := by
  change ({0} : Finset (Fin 2)).Nonempty
  exact ⟨0, by simp⟩

theorem byzantine_nonempty : (Finset.univ \ rho.honest).Nonempty := by
  change (Finset.univ \ ({0} : Finset (Fin 2))).Nonempty
  exact ⟨1, by simp⟩

theorem event_mem_shape {e : Event (Fin 2)} (he : e ∈ rho.events) :
    ∃ n : Nat, n < eventCount + 1 ∧ e = .tick 0 (n : Time) := by
  have he' : e ∈ events := he
  rw [events] at he'
  obtain ⟨n, hn0, hn1, hne⟩ := tickEvents_mem 0 (eventCount + 1) e he'
  exact ⟨n, by simpa using hn1, hne⟩

theorem event_at_shape {i : Nat} {e : Event (Fin 2)}
    (he : rho.events[i]? = some e) :
    ∃ n : Nat, n < eventCount + 1 ∧ e = .tick 0 (n : Time) := by
  exact event_mem_shape (List.mem_of_getElem? he)

theorem event_at_tick {i : Nat} {e : Event (Fin 2)}
    (he : rho.events[i]? = some e) :
    ∃ k : Nat, e = Event.tick 0 (k : Time) := by
  obtain ⟨k, -, hk⟩ := event_at_shape he
  exact ⟨k, hk⟩

theorem schedule_sorted : rho.events.Pairwise
    (fun e f => NamedEvent.key e ≤ NamedEvent.key f) := by
  have hEvents : rho.events = tickEvents 0 (eventCount + 1) := by
    rfl
  rw [hEvents]
  exact tickEvents_pairwise 0 (eventCount + 1)

theorem schedule_nodup : rho.events.Nodup := by
  have hEvents : rho.events = tickEvents 0 (eventCount + 1) := by
    rfl
  rw [hEvents]
  exact tickEvents_nodup 0 (eventCount + 1)

theorem horizon_nonneg : 0 ≤ horizon := by
  norm_num [horizon]

theorem eventCount_coe : (eventCount : Time) = horizon := by
  simp only [eventCount]
  exact Int.toNat_of_nonneg horizon_nonneg

theorem schedule_in_horizon :
    ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := event_mem_shape he
  change 0 ≤ (n : Time) ∧ (n : Time) ≤ horizon
  constructor
  · exact_mod_cast (Nat.zero_le n)
  · rw [← eventCount_coe]
    exact_mod_cast (Nat.le_of_lt_succ hn)

theorem schedule_honest_only :
    ∀ e ∈ rho.events, e.node ∈ rho.honest := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := event_mem_shape he
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem schedule_tick_public :
    ∀ v t, .tick v t ∈ rho.events → PublicTime S t := by
  intro v t he
  obtain ⟨n, hn, hne⟩ := event_mem_shape he
  cases hne
  exact ⟨n, by norm_num [PublicTime, S, E]⟩

theorem schedule_tick_total :
    ∀ v ∈ rho.honest, ∀ t, PublicTime S t → 0 ≤ t → t ≤ rho.horizon →
      .tick v t ∈ rho.events := by
  intro v hv t ht hnonneg hhor
  change t ≤ horizon at hhor
  have hv0 : v = 0 := by
    change v ∈ ({0} : Finset (Fin 2)) at hv
    simpa using hv
  subst v
  rcases ht with ⟨n, hn⟩
  have hnt : t = (n : Time) := by simpa [S, E] using hn
  have hnle : (n : Time) ≤ (eventCount : Time) := by
    calc
      (n : Time) = t := hnt.symm
      _ ≤ horizon := hhor
      _ = (eventCount : Time) := eventCount_coe.symm
  have hnlt : n < eventCount + 1 := by
    have hnle' : n ≤ eventCount := by exact_mod_cast hnle
    omega
  rw [hnt]
  have hEvents : rho.events = tickEvents 0 (eventCount + 1) := by rfl
  rw [hEvents]
  exact tickEvents_mem_of_time 0 (eventCount + 1) n (by omega) (by omega)

/-! ## Delivery and committee/weight primitives -/

theorem delivery_wire : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.wellFormed S o = true := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_at_shape he
  cases hne

theorem delivery_deps : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.depsPresent (NamedRun.stateBefore S rho i v).st o = true := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_at_shape he
  cases hne

theorem delivery_fresh : ∀ (i : Nat) (v : Fin 2) (o : NamedObject (Fin 2))
    (t : Time), rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o = false := by
  intro i v o t he
  obtain ⟨n, hn, hne⟩ := event_at_shape he
  cases hne

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

theorem below_one_third : BelowOneThird S rho.honest := by
  rw [BelowOneThird, total_weight_eq, byzantine_weight_eq]
  norm_num

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

theorem timeout_bound : TimeoutDelayBound S extra := by
  norm_num [TimeoutDelayBound, extra, S, hc, cfg]

theorem recurrence : ProposerOpeningCarrierRecurrence S rho gap := by
  intro k _ _
  refine ⟨k + 2, le_rfl, by simp [gap], ?_⟩
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
    (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
      ((0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
        (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
          (0 : Fin 2) ∈ ({0} : Finset (Fin 2)))
  simp

/-- Gap 2 is impossible because its continuous-time admissible window can
collapse to the single point `t + 2 * period`; the strong witness therefore
uses gap 3. -/
theorem generic_opening_recurrence_gap_two_impossible :
    ¬ Statements.Generic.StrongMultiProposerRecurrence
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 2 := by
  intro h
  obtain ⟨s, hlo, hhi, hcarrier, _hopen⟩ := h 1 (by norm_num) (by
    norm_num [Statements.Instantiation.constants, S, E, hc, cfg, rho, horizon,
      Protocol.proposal_time, Env.t, slotStart, Setup.a, Protocol.HealConfig.a,
      Protocol.HealConfig.opening_slot])
  change (∃ r : Round, s = S.hc.opening_slot r) ∧ _ at hcarrier
  obtain ⟨r, hs⟩ := hcarrier.1
  rw [hs] at hlo hhi
  norm_num [Statements.Instantiation.constants, Statements.Instantiation.interface,
    S, E, hc, Protocol.proposal_time, Env.t, slotStart,
    Protocol.HealConfig.opening_slot, Setup.a, Protocol.HealConfig.a] at hlo hhi
  have heq : 4 * ((r : Time) * 3) = 25 := le_antisymm hhi hlo
  have heqNat : 4 * (r * 3) = 25 := by exact_mod_cast heq
  norm_num [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at heqNat
  have hmod := congrArg (fun n : Nat => n % 12) heqNat
  norm_num [Nat.mul_mod] at hmod

theorem gap_bound : gap + 2 ≤ S.cfg.K := by
  norm_num [gap, S, cfg]

theorem no_delivery_event {i : Nat} {v : Fin 2} {o : NamedObject (Fin 2)}
    {t : Time} (he : rho.events[i]? = some (.deliver v o t)) : False := by
  obtain ⟨n, hn, hshape⟩ := event_at_shape he
  cases hshape

theorem emitted_node_zero {v : Fin 2} {o : NamedObject (Fin 2)} {t : Time}
    (hemit : NamedRun.emits S rho v o t) : v = 0 := by
  obtain ⟨i, hi, hmem⟩ := hemit
  obtain ⟨n, hn, hshape⟩ := event_mem_shape
    (List.mem_of_getElem? hi)
  have hnode := congrArg NamedEvent.node hshape
  simpa only [NamedEvent.node] using hnode

theorem emitted_gf_honest {v : Fin 2} {u : GoldfishVote (Fin 2)} {t : Time}
    (hemit : NamedRun.emits S rho v (.gfVote u) t) :
    u.val_index ∈ rho.honest := by
  have hv : v = 0 := emitted_node_zero hemit
  have hval : u.val_index = v :=
    (Proofs.Optimistic.emits_gfVote_shape S hemit).2.2.1
  rw [hval, hv]
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem emitted_attest_honest {v : Fin 2} {a : NamedAttestation (Fin 2)} {t : Time}
    (hemit : NamedRun.emits S rho v (.attest a) t) :
    a.val_index ∈ rho.honest := by
  have hv : v = 0 := emitted_node_zero hemit
  have ha := (Proofs.Optimistic.emits_attest_shape S hemit).1
  rw [ha, hv]
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem schedule_well_formed : ScheduleWellFormed S rho :=
  { sorted := schedule_sorted
    horizon_nonneg := by decide
    nodup := schedule_nodup
    in_horizon := schedule_in_horizon
    honest_only := schedule_honest_only
    tick_public := schedule_tick_public
    tick_total := schedule_tick_total }

theorem delivery_well_formed : DeliveryWellFormed S rho :=
  { wire := delivery_wire
    deps := delivery_deps
    fresh := delivery_fresh }

theorem process_is_emission {v : Fin 2} {o : NamedObject (Fin 2)} {t : Time}
    (h : NamedRun.processes S rho v o t) :
    NamedRun.emits S rho v o t := by
  rcases h with h | ⟨i, hi⟩
  · exact h
  · exact (no_delivery_event hi).elim

theorem self_handles_of_emission {i : Nat} {o : Object (Fin 2)} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t))
    (ho : o ∈ NamedRun.emittedAt S rho i 0 t) :
    NamedRun.actualHandlesAt S rho i 0 o t := by
  refine ⟨?_, ⟨.tick 0 t, hi, rfl, rfl⟩⟩
  cases o with
  | block B => exact Or.inl ⟨t, hi, ho⟩
  | gfVote u => exact Or.inl (Or.inl ⟨t, hi, ho⟩)
  | attest a => exact Or.inl (Or.inl ⟨t, hi, ho⟩)

theorem sync_deadline_strict (t : Time) :
    t < max t S.E.t_GST + S.E.Δ := by
  change t < max t 0 + 1
  by_cases h : t ≤ 0
  · rw [max_eq_right h]
    exact lt_of_le_of_lt h (by norm_num)
  · rw [max_eq_left (le_of_not_ge h)]
    exact lt_add_of_pos_right _ (by norm_num)

theorem synchrony : Synchrony S rho where
  broadcast := by
    intro v hv o t hemit w hw hdeadline _hguard
    have hv0 : v = 0 := by simpa [rho] using hv
    have hw0 : w = 0 := by simpa [rho] using hw
    subst v
    subst w
    obtain ⟨i, hi, ho⟩ := hemit
    refine ⟨t, le_rfl, sync_deadline_strict t, i,
      self_handles_of_emission hi ho⟩
  relay_block := by
    intro v hv i B t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := by simpa [rho] using hv
    have hw0 : w = 0 := by simpa [rho] using hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := by simpa [rho] using hv
    have hw0 : w = 0 := by simpa [rho] using hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩
  relay_attest := by
    intro v hv i a t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := by simpa [rho] using hv
    have hw0 : w = 0 := by simpa [rho] using hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩

theorem emitted_block_payload_fields {i : Nat} {v : Fin 2} {t : Time}
    {B : NamedBlock (Fin 2)}
    (_hi : rho.events[i]? = some (.tick v t))
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i v t) :
    B.attestations =
      Protocol.NamedProposalRows.proposalRows B.parent
        (Protocol.NamedProposalRows.select .poolAndCarried hc
          (NamedActionReads.confirmationReadFrom
            S (NamedRun.stateBefore S rho i v) t).st) := by
  have hmem := Proofs.HealingSurface.block_mem_on_tick_emit S v
    (NamedRun.stateBefore S rho i v) t hB
  obtain ⟨_, hDuty⟩ := hmem
  let gc := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).cache
  have hproposal : Protocol.NamedActions.proposal_with gc
      .poolAndCarried S.E S.hc (S.node v)
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hDuty
    generalize hP : Protocol.NamedActions.proposal_with gc .poolAndCarried
      S.E S.hc (S.node v)
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st = P at hDuty
    cases P with
    | none => simp at hDuty
    | some X =>
        have hXB : X = B := Option.some.inj hDuty
        exact congrArg some hXB
  have hp := Proofs.NamedActions.proposal_payload gc .poolAndCarried
    S.E S.hc (S.node v)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st B hproposal
  dsimp only at hp
  exact hp.2.2.2.2.2.2.1

theorem ancestor_body_mem_local {st : Protocol.NamedStore (Fin 2)}
    (hpc : Proofs.NamedStore.NamedParentClosed st) {A B : NamedBlock (Fin 2)}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      have hA : A = NamedBlock.genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hAB
      subst A
      exact hB
  | node parent s root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

theorem proposal_root_of_output
    (v : Fin 2)
    (contract : Protocol.GradeContract (Fin 2))
    (st : Protocol.NamedStore (Fin 2)) {B : NamedBlock (Fin 2)}
    (hB : (Protocol.NamedDuties.propose_block_with contract S.E S.hc S.cfg
      (S.node v) st).2 = some B) :
    B.root = (S.node v).new_root st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with at hB
  generalize hP : Protocol.NamedActions.proposal_with contract .poolAndCarried
    S.E S.hc (S.node v) st = P at hB
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

theorem emitted_block_root_shape {v : Fin 2} {B : NamedBlock (Fin 2)} {t : Time}
    (hemit : NamedRun.emits S rho v (.block B) t) :
    B.root = ⟨B.slot + 1⟩ := by
  obtain ⟨i, hi, hmem⟩ := hemit
  obtain ⟨_, hDuty⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S v
    (NamedRun.stateBefore S rho i v) t hmem
  have hroot := proposal_root_of_output
    v
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).cache)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st hDuty
  have hslot := Proofs.HealingSurface.propose_block_with_slot
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).cache)
    S.E S.hc S.cfg (S.node v)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st hDuty
  rw [hroot, ← hslot]
  rfl

theorem block_emission_of_run_block {B : NamedBlock (Fin 2)}
    (hB : NamedRun.blockInRun S rho B)
    (hgen : B ≠ NamedBlock.genesis) :
    ∃ t : Time, NamedRun.emits S rho 0 (.block B) t := by
  obtain ⟨C, hC, hBC⟩ := hB
  rcases hC with hobject | ⟨v, hv, i, hCbody⟩
  · obtain ⟨j, u, t, hdeliver⟩ :=
      Proofs.Bridges.exists_deliver_of_mem_objects rho hobject
    exact (no_delivery_event hdeliver).elim
  · have hInv := Proofs.NamedRuntime.stateBefore_invariants S rho i v
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
        (NamedRun.stateBefore S rho i v).st := hInv.1.1.1
    have hBbody : B ∈ (NamedRun.stateBefore S rho i v).st.bodies :=
      ancestor_body_mem_local hcoh.2.2.1 hCbody hBC
    rcases Proofs.Bridges.processes_block_of_mem_T S rho v i B
        hBbody with hgen' | ⟨j, e, hj, hje, hproc⟩
    · exact (hgen hgen').elim
    · obtain ⟨k, hk, hmem⟩ := process_is_emission hproc
      have hv0 := emitted_node_zero (process_is_emission hproc)
      subst v
      exact ⟨e.time, k, hk, hmem⟩

theorem run_block_root_shape {B : NamedBlock (Fin 2)}
    (hB : NamedRun.blockInRun S rho B) :
    B = NamedBlock.genesis ∨ B.root = ⟨B.slot + 1⟩ := by
  by_cases hgen : B = NamedBlock.genesis
  · exact Or.inl hgen
  · right
    obtain ⟨t, hemit⟩ := block_emission_of_run_block hB hgen
    exact emitted_block_root_shape hemit

theorem root_collision_free : RootCollisionFree S rho := by
  refine ⟨?_⟩
  intro B C hB hC A D hA hD hroot
  have hArun : NamedRun.blockInRun S rho A :=
    by
      rcases hA with hAB | hAC
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hAB
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hAC
  have hDrun : NamedRun.blockInRun S rho D :=
    by
      rcases hD with hDB | hDC
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB hDB
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC hDC
  rcases run_block_root_shape hArun with rfl | hAroot
  · rcases run_block_root_shape hDrun with rfl | hDroot
    · rfl
    · have hvalue := congrArg BlockId.value hroot
      rw [hDroot] at hvalue
      simp [NamedBlock.root, genesisRoot] at hvalue
  · rcases run_block_root_shape hDrun with rfl | hDroot
    · have hvalue := congrArg BlockId.value hroot
      rw [hAroot] at hvalue
      simp [NamedBlock.root, genesisRoot] at hvalue
    · have hslot : A.slot = D.slot := by
        have hvalue := congrArg BlockId.value hroot
        simp [hAroot, hDroot] at hvalue
        omega
      obtain ⟨tA, hAemit⟩ := block_emission_of_run_block hArun (by
        intro h
        subst A
        have hvalue := congrArg BlockId.value hAroot
        simp [NamedBlock.root, genesisRoot] at hvalue)
      obtain ⟨tD, hDemit⟩ := block_emission_of_run_block hDrun (by
        intro h
        subst D
        have hvalue := congrArg BlockId.value hDroot
        simp [NamedBlock.root, genesisRoot] at hvalue)
      exact Proofs.HealingSurface.emits_block_unique S schedule_well_formed
        hAemit hDemit hslot



def EmitBefore (i : Nat) (o : Object (Fin 2)) : Prop :=
  ∃ j : Nat, j < i ∧ ∃ t : Time,
    rho.events[j]? = some (.tick 0 t) ∧
      o ∈ NamedRun.emittedAt S rho j 0 t

structure OriginState (i : Nat) : Prop where
  body : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S rho i 0).st.bodies →
      B = NamedBlock.genesis ∨ EmitBefore i (.block B)
  body_gf : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S rho i 0).st.bodies →
      ∀ u : GoldfishVote (Fin 2), u ∈ B.gf_votes →
        EmitBefore i (.gfVote u)
  body_row : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S rho i 0).st.bodies →
      ∀ a : NamedAttestation (Fin 2), a ∈ B.attestations →
        EmitBefore i (.attest a)
  gf : ∀ k : Slot, ∀ u : GoldfishVote (Fin 2),
    u ∈ (NamedRun.stateBefore S rho i 0).st.core.pool k →
      EmitBefore i (.gfVote u)
  row : ∀ k : Round, ∀ a : NamedAttestation (Fin 2),
    a ∈ (NamedRun.stateBefore S rho i 0).st.sg_rows k →
      EmitBefore i (.attest a)

theorem emitBefore_mono {i j : Nat} (hij : i ≤ j) {o : Object (Fin 2)}
    (h : EmitBefore i o) : EmitBefore j o := by
  rcases h with ⟨k, hki, t, he, ho⟩
  exact ⟨k, hki.trans_le hij, t, he, ho⟩

theorem emitBefore_emits {i : Nat} {o : Object (Fin 2)}
    (h : EmitBefore i o) : ∃ t : Time, NamedRun.emits S rho 0 o t := by
  rcases h with ⟨j, -, t, he, ho⟩
  exact ⟨t, ⟨j, he, ho⟩⟩

theorem event_key_le_of_index {j i : Nat} {ej ei : Event (Fin 2)}
    (hji : j < i) (hej : rho.events[j]? = some ej)
    (hei : rho.events[i]? = some ei) :
    NamedEvent.key ej ≤ NamedEvent.key ei := by
  have hjlen : j < rho.events.length :=
    (List.getElem?_eq_some_iff.mp hej).1
  have hilen : i < rho.events.length :=
    (List.getElem?_eq_some_iff.mp hei).1
  have hp := (List.pairwise_iff_get.mp schedule_sorted)
    (⟨j, hjlen⟩ : Fin rho.events.length)
    (⟨i, hilen⟩ : Fin rho.events.length) (by exact_mod_cast hji)
  have hgj : rho.events.get ⟨j, hjlen⟩ = ej := by
    rw [List.get_eq_getElem]
    have h := hej
    rw [List.getElem?_eq_getElem hjlen] at h
    exact Option.some.inj h
  have hgi : rho.events.get ⟨i, hilen⟩ = ei := by
    rw [List.get_eq_getElem]
    have h := hei
    rw [List.getElem?_eq_getElem hilen] at h
    exact Option.some.inj h
  rw [← hgj, ← hgi]
  exact hp

theorem emitBefore_time_le {i : Nat} {o : Object (Fin 2)} {t : Time}
    (he : rho.events[i]? = some (.tick 0 t)) (h : EmitBefore i o) :
    ∃ t' : Time, t' ≤ t ∧ NamedRun.emits S rho 0 o t' := by
  rcases h with ⟨j, hji, t', hej, ho⟩
  have hkey := event_key_le_of_index hji hej he
  have htime : t' ≤ t := by
    have hlex : toLex (t', 0) ≤ toLex (t, 0) := by
      simpa [NamedEvent.key, NamedEvent.time, NamedEvent.phase] using hkey
    rcases Prod.Lex.toLex_le_toLex.mp hlex with hlt | heq
    · exact le_of_lt hlt
    · exact le_of_eq heq.1
  exact ⟨t', htime, ⟨j, hej, ho⟩⟩

theorem orderedBodies_mem {st : Protocol.NamedStore (Fin 2)}
    {B : NamedBlock (Fin 2)}
    (hB : B ∈ Protocol.NamedProposalRows.orderedBodies st) :
    B ∈ st.bodies := by
  unfold Protocol.NamedProposalRows.orderedBodies at hB
  simp only [List.mem_filterMap] at hB
  obtain ⟨root, hroot, hfind⟩ := hB
  exact Proofs.Engine.pickUnique?_mem hfind

theorem emitted_block_gf_origin {i : Nat} {t : Time} {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S rho i 0 t)
    (hstate : OriginState i) {u : GoldfishVote (Fin 2)}
    (hu : u ∈ B.gf_votes) : EmitBefore i (.gfVote u) := by
  have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S rho i 0) t hB
  have hproposal :
      Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hshape
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st with
    | none => simp [hp] at hshape
    | some C =>
        simp [hp] at hshape ⊢
        exact hshape.2
  have hp := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st B hproposal
  rcases hp with ⟨-, -, -, -, hgf, -, -, -⟩
  have hfields := Proofs.DutyInputDefaults.proposal_input_fields
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).cache)
    S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st.core.toHealing
  have hgf' : B.gf_votes =
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).st.core.gf_votes
        ((NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st.core.s - 1) := by
    calc
      B.gf_votes = (Protocol.proposal_input_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st.core.toHealing).gf_votes := hgf
      _ = Protocol.proposer_view
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st.core.toHealing.toFG.toSG.toGoldfishStore
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st.core.toHealing.s :=
          hfields.2.2.2.1
      _ = (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st.core.gf_votes
          ((NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).st.core.s - 1) := by rfl
  have hu' : u ∈ (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st.core.gf_votes
      ((NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).st.core.s - 1) := by
    rw [← hgf']
    exact hu
  exact hstate.gf _ _ (by simpa [NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, Protocol.Store.pool] using hu')

theorem emitted_block_row_origin {i : Nat} {t : Time} {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S rho i 0 t)
    (hstate : OriginState i) {a : NamedAttestation (Fin 2)}
    (ha : a ∈ B.attestations) : EmitBefore i (.attest a) := by
  have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S rho i 0) t hB
  have hproposal :
      Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hshape
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st with
    | none => simp [hp] at hshape
    | some C =>
        simp [hp] at hshape ⊢
        exact hshape.2
  have hp := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S rho i 0) t).st B hproposal
  rcases hp with ⟨-, -, -, -, -, -, hrows, -⟩
  have hsel : a ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).st := by
    exact (Proofs.NamedProposalRows.mem_proposalRows B.parent _ a (hrows ▸ ha)).1
  have hsource : a ∈ Protocol.NamedProposalRows.poolRows S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i 0) t).st ∨
      a ∈ Protocol.NamedProposalRows.carriedRows S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st := by
    simpa [Protocol.NamedProposalRows.select] using hsel
  rcases hsource with hpool | hcarried
  · have hprocessed : a ∈ Protocol.NamedProposalRows.processedRows S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i 0) t).st :=
      (List.mem_filter.mp hpool).1
    unfold Protocol.NamedProposalRows.processedRows at hprocessed
    obtain ⟨r, hr, hrow⟩ := List.mem_flatMap.mp hprocessed
    exact hstate.row r a (by simpa [NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hrow)
  · unfold Protocol.NamedProposalRows.carriedRows at hcarried
    obtain ⟨C, hC, hrow⟩ := List.mem_flatMap.mp hcarried
    split at hrow
    · have hrow' := (List.mem_filter.mp hrow).1
      have hC' : C ∈ (NamedRun.stateBefore S rho i 0).st.bodies := by
        simpa [NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using orderedBodies_mem hC
      exact hstate.body_row C hC' a hrow'
    · simp at hrow

theorem originState_tick {i k : Nat}
    (he : rho.events[i]? = some (.tick 0 (k : Time)))
    (hstate : OriginState i) : OriginState (i + 1) := by
  let n := NamedRun.stateBefore S rho i 0
  let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing
    (k : Time) n.cache
  let gc := DecoupledConsensusModel.Protocol.frameContract c
  let out := Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node 0)
    n.st n.record (k : Time)
  have hout : out.1 = (NamedRun.stateBefore S rho (i + 1) 0).st := by
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
    rfl
  have emit_out : ∀ {o : Object (Fin 2)}, o ∈ out.2.2 →
      o ∈ NamedRun.emittedAt S rho i 0 (k : Time) := by
    intro o ho
    change o ∈ (NamedNode.tick S 0
      (NamedRun.stateBefore S rho i 0) (k : Time)).2
    exact ho
  refine {
    body := ?_
    body_gf := ?_
    body_row := ?_
    gf := ?_
    row := ?_ }
  · intro B hB
    have hB' : B ∈ out.1.bodies := by
      rw [hout]
      exact hB
    by_cases hpre : B ∈ n.st.bodies
    · rcases hstate.body B hpre with hgen | horigin
      · exact Or.inl hgen
      · exact Or.inr (emitBefore_mono (Nat.le_succ _) horigin)
    · have hnew := Proofs.Bridges.on_tick_emit_T_mem S 0 n (k : Time) (by
        simpa only [NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact Or.inr ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [NamedNode.tick, n, c, gc, out] using hem)⟩
  · intro B hB u hu
    have hB' : B ∈ out.1.bodies := by
      rw [hout]
      exact hB
    by_cases hpre : B ∈ n.st.bodies
    · exact emitBefore_mono (Nat.le_succ _)
        (hstate.body_gf B hpre u hu)
    · have hnew := Proofs.Bridges.on_tick_emit_T_mem S 0 n (k : Time) (by
        simpa only [NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_gf_origin (i := i) (t := (k : Time))
          (by simpa only [NamedNode.tick, n, c, gc, out] using hem)
          hstate hu)
  · intro B hB a ha
    have hB' : B ∈ out.1.bodies := by
      rw [hout]
      exact hB
    by_cases hpre : B ∈ n.st.bodies
    · exact emitBefore_mono (Nat.le_succ _)
        (hstate.body_row B hpre a ha)
    · have hnew := Proofs.Bridges.on_tick_emit_T_mem S 0 n (k : Time) (by
        simpa only [NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_row_origin (i := i) (t := (k : Time))
          (by simpa only [NamedNode.tick, n, c, gc, out] using hem)
          hstate ha)
  · intro k' u hu
    have hstamps : Protocol.PoolStamps
        (NamedRun.stateBefore S rho (i + 1) 0).st.core :=
      Protocol.poolStamps_stateBefore S schedule_well_formed 0 (i + 1)
    have hu_list : u ∈
        (NamedRun.stateBefore S rho (i + 1) 0).st.core.gf_votes k' := by
      simpa [Protocol.Store.pool] using hu
    have hslot : u.slot = k' := hstamps.slot k' u hu_list
    by_cases hpre : u ∈ n.st.core.pool u.slot
    · exact emitBefore_mono (Nat.le_succ _)
        (hstate.gf u.slot u hpre)
    · have huout : u ∈ out.1.core.pool u.slot := by
        rw [hout]
        change u ∈ (NamedRun.stateBefore S rho (i + 1) 0).st.core.pool u.slot
        simpa [hslot] using hu
      have hnew := Proofs.NamedReceiptCallsGF.tick_new_vote_origin gc S.E S.hc
        S.cfg (S.node 0) n.st n.record (k : Time) u hpre (by
          simpa only [out] using huout)
      rcases hnew with hdirect | ⟨B, hblock, hnot, hpost⟩
      · exact ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [out] using hdirect)⟩
      · have hblock' : Object.block B ∈
            NamedRun.emittedAt S rho i 0 (k : Time) :=
          emit_out (by simpa only [out] using hblock)
        exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_gf_origin (i := i) (t := (k : Time)) hblock' hstate
          (by
            have hcall := Proofs.NamedReceiptCallsBase.blockCallAt_self S rho he
              (by simpa only [out] using hblock)
            have horigin := Proofs.NamedReceiptCallsGF.block_with_new_vote_origin
              S rho i 0 B
              (NamedActionReads.confirmationReadFrom S n (k : Time)).st
              hcall u (by
                simpa [NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock, n] using hpre) hpost
            obtain ⟨j, hj⟩ := horigin
            exact List.mem_of_getElem? hj.2.2.2))
  · intro k' a ha
    have haout : a ∈ out.1.sg_rows a.round := by
      rw [hout]
      rw [Proofs.NamedStoreBridge.sgRowRounds_stateBefore S rho
        (i + 1) 0 k' a ha]
      exact ha
    by_cases hheld : a ∈ n.st.sg_rows a.round
    · exact emitBefore_mono (Nat.le_succ _) (hstate.row a.round a hheld)
    · have hnew := Proofs.NamedReceiptCallsF1.tick_new_full_row_origin gc S.E S.hc
        S.cfg (S.node 0) n.st n.record (k : Time) a hheld (by
          simpa only [out] using haout)
      rcases hnew with hdirect | ⟨B, hblock, hnot, hpost⟩
      · exact ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [out] using hdirect)⟩
      · have hblock' : Object.block B ∈
            NamedRun.emittedAt S rho i 0 (k : Time) :=
          emit_out (by simpa only [out] using hblock)
        exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_row_origin (i := i) (t := (k : Time)) hblock' hstate
          (by
            have hcall := Proofs.NamedReceiptCallsBase.blockCallAt_self S rho he
              (by simpa only [out] using hblock)
            have horigin := Proofs.NamedReceiptCallsF1.block_full_marker_origin
              S rho i 0 B
              (NamedActionReads.confirmationReadFrom S n (k : Time)).st a hcall
              (by simpa [NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, n] using hheld) (by
                simpa [NamedReceipt.process, n] using hpost)
            obtain ⟨j, hj, -, -⟩ := horigin
            exact List.mem_of_getElem? hj.2.2.2))

theorem originState : ∀ i : Nat, OriginState i := by
  intro i
  induction i with
  | zero =>
      refine {
        body := ?_
        body_gf := ?_
        body_row := ?_
        gf := ?_
        row := ?_ }
      · intro B hB
        have hgen : B = NamedBlock.genesis := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial] using hB
        exact Or.inl hgen
      · intro B hB u hu
        have hgen : B = NamedBlock.genesis := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial] using hB
        subst B
        have hfalse : False := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial, NamedBlock.gf_votes] using hu
        exact hfalse.elim
      · intro B hB a ha
        have hgen : B = NamedBlock.genesis := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial] using hB
        subst B
        have hfalse : False := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial, NamedBlock.attestations] using ha
        exact hfalse.elim
      · intro k u hu
        have hfalse : False := by
          simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial, Protocol.Store.pool, Protocol.Store.init] using hu
        exact hfalse.elim
      · intro k a ha
        simpa [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
          Protocol.NamedStore.initial, NamedBlock.attestations] using ha
  | succ i ih =>
      cases he : rho.events[i]? with
      | none =>
          have hsame : NamedRun.stateBefore S rho (i + 1) 0 =
              NamedRun.stateBefore S rho i 0 := by
            unfold NamedRun.stateBefore
            rw [List.take_add_one, he, List.foldl_append]
            rfl
          refine {
            body := ?_
            body_gf := ?_
            body_row := ?_
            gf := ?_
            row := ?_ }
          · intro B hB
            exact ih.body B (by simpa [hsame] using hB) |>.elim
              (fun h => Or.inl h) (fun h => Or.inr (emitBefore_mono (Nat.le_succ _) h))
          · intro B hB u hu
            exact emitBefore_mono (Nat.le_succ _)
              (ih.body_gf B (by simpa [hsame] using hB) u hu)
          · intro B hB a ha
            exact emitBefore_mono (Nat.le_succ _)
              (ih.body_row B (by simpa [hsame] using hB) a ha)
          · intro k u hu
            exact emitBefore_mono (Nat.le_succ _)
              (ih.gf k u (by simpa [hsame] using hu))
          · intro k a ha
            exact emitBefore_mono (Nat.le_succ _)
              (ih.row k a (by simpa [hsame] using ha))
      | some e =>
          obtain ⟨k, hk⟩ := event_at_tick he
          rw [hk] at he
          exact originState_tick he ih

theorem emitted_block_slot_read {i : Nat} {v : Fin 2} {t : Time}
    {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S rho i v t) :
    B.slot = (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st.core.s := by
  have hmem := Proofs.HealingSurface.block_mem_on_tick_emit S v
    (NamedRun.stateBefore S rho i v) t hB
  obtain ⟨-, hDuty⟩ := hmem
  exact Proofs.HealingSurface.propose_block_with_slot
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).cache)
    S.E S.hc S.cfg (S.node v)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st hDuty

theorem emitted_block_gf_votes_fields {i : Nat} {v : Fin 2} {t : Time}
    {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S rho i v t) :
    B.gf_votes =
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.gf_votes
        ((NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho i v) t).st.core.s - 1) := by
  have hmem := Proofs.HealingSurface.block_mem_on_tick_emit S v
    (NamedRun.stateBefore S rho i v) t hB
  obtain ⟨-, hDuty⟩ := hmem
  let gc := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).cache
  have hproposal : Protocol.NamedActions.proposal_with gc
      .poolAndCarried S.E S.hc (S.node v)
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hDuty
    generalize hP : Protocol.NamedActions.proposal_with gc .poolAndCarried
      S.E S.hc (S.node v)
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st = P at hDuty
    cases P with
    | none => simp at hDuty
    | some X =>
        have hXB : X = B := Option.some.inj hDuty
        exact congrArg some hXB
  have hp := Proofs.NamedActions.proposal_payload gc .poolAndCarried
    S.E S.hc (S.node v)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st B hproposal
  dsimp only at hp
  rcases hp with ⟨-, -, -, -, hgf, -, -, -⟩
  have hfields := Proofs.DutyInputDefaults.proposal_input_fields gc
    S.E S.hc (S.node v)
    (NamedActionReads.confirmationReadFrom
      S (NamedRun.stateBefore S rho i v) t).st.core.toHealing
  calc
    B.gf_votes = (Protocol.proposal_input_with gc S.E S.hc (S.node v)
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.toHealing).gf_votes := hgf
    _ = Protocol.proposer_view
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.toHealing.toFG.toSG.toGoldfishStore
      (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.toHealing.s :=
          hfields.2.2.2.1
    _ = (NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.gf_votes
        ((NamedActionReads.confirmationReadFrom
        S (NamedRun.stateBefore S rho i v) t).st.core.s - 1) := by rfl



theorem authentic : Unforgeable S rho := by
  refine {
    unforgeable := ?_
    carried_gf := ?_
    carried_attest := ?_ }
  · intro v o t hproc author hhon hauthor
    have hem : NamedRun.emits S rho v o t := process_is_emission hproc
    have hv0 : v = 0 := emitted_node_zero hem
    have ha0 : author = 0 := by
      change author ∈ ({0} : Finset (Fin 2)) at hhon
      simpa using hhon
    subst v
    subst author
    exact ⟨t, le_rfl, hem⟩
  · intro v B t hproc u hu hhon
    have hem : NamedRun.emits S rho v (.block B) t := process_is_emission hproc
    have hv0 : v = 0 := emitted_node_zero hem
    subst v
    obtain ⟨i, hi, hmem⟩ := hem
    have horigin := emitted_block_gf_origin (i := i) (t := t) hmem
      (originState i) hu
    obtain ⟨sent, hsent, hemit⟩ := emitBefore_time_le hi horigin
    have hval := (Proofs.Optimistic.emits_gfVote_shape S hemit).2.2.1
    refine ⟨sent, hsent, ?_⟩
    simpa [hval] using hemit
  · intro v B t hproc a ha hhon
    have hem : NamedRun.emits S rho v (.block B) t := process_is_emission hproc
    have hv0 : v = 0 := emitted_node_zero hem
    subst v
    obtain ⟨i, hi, hmem⟩ := hem
    have horigin := emitted_block_row_origin (i := i) (t := t) hmem
      (originState i) ha
    obtain ⟨sent, hsent, hemit⟩ := emitBefore_time_le hi horigin
    have hval := (Proofs.Optimistic.emits_attest_shape S hemit).1
    refine ⟨sent, hsent, ?_⟩
    simpa [hval] using hemit

/-! ## The assembled admissible and strong-finality premises -/

theorem admissible_core : AdmissibleCore S rho := by
  refine {
    toNamedScheduleWellFormed := schedule_well_formed
    toNamedDeliveryWellFormed := delivery_well_formed
    toNamedRootCollisionFree := root_collision_free
    toNamedUnforgeable := authentic }

theorem admissible : Admissible S rho := by
  exact
    { toExecutionValid := admissible_core
      toNamedSynchrony := synchrony
      all_awake := by
        intro v hv r hpost hhor
        have hv0 : v = 0 := by
          change v ∈ ({0} : Finset (Fin 2)) at hv
          simpa using hv
        subst v
        exact honest_awake r }

theorem strong_finality_run : StrongFinalityRun S rho gap := by
  refine {
    execution := admissible_core
    synchrony := synchrony
    allAwake := admissible.all_awake
    committees := honest_committee_majority
    belowThird := below_one_third
    recurrence := recurrence
    gapBound := gap_bound }

theorem gst_zero : S.E.t_GST = 0 := by
  rfl

theorem generic_finality_regime :
    Statements.Generic.FinalityRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 3 := by
  have hrec : Statements.Generic.StrongMultiProposerRecurrence
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 3 := by
    intro t ht _
    have hperiod : 0 < (Statements.Instantiation.constants S).period :=
      Proofs.concretePeriod_pos S
    let q : Nat := Int.toNat (t / (Statements.Instantiation.constants S).period)
    have hquot : 0 ≤ t / (Statements.Instantiation.constants S).period :=
      Int.ediv_nonneg ht hperiod.le
    have hqcast : (q : Time) =
        t / (Statements.Instantiation.constants S).period := by
      dsimp [q]
      exact Int.toNat_of_nonneg hquot
    have hlow : (q : Time) * (Statements.Instantiation.constants S).period ≤ t := by
      rw [hqcast]
      exact Int.ediv_mul_le _ (ne_of_gt hperiod)
    have hupp : t <
        ((q + 1 : Nat) : Time) * (Statements.Instantiation.constants S).period := by
      have h := Int.lt_ediv_add_one_mul_self t hperiod
      rw [← hqcast] at h
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using h
    have hproposalTime : ∀ r : Round,
        Protocol.proposal_time S.E (S.hc.opening_slot r) =
          (r : Time) * (Statements.Instantiation.constants S).period := by
      intro r
      change Protocol.proposal_time S.E (S.hc.opening_slot r) =
        (r : Time) * (S.a 1 - S.a 0)
      unfold Protocol.proposal_time Env.t DecoupledConsensusModel.slotStart
        Protocol.HealConfig.opening_slot Setup.a Protocol.HealConfig.a
      simp only [DecoupledConsensusModel.slotStart, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    let r : Round := q + 3
    refine ⟨S.hc.opening_slot r, ?_, ?_, ?_, ?_⟩
    · change t + 2 * (Statements.Instantiation.constants S).period ≤
        Protocol.proposal_time S.E (S.hc.opening_slot r)
      rw [hproposalTime]
      dsimp [r]
      have hupper := add_lt_add_right hupp
        (2 * (Statements.Instantiation.constants S).period)
      norm_num [Nat.cast_add, Nat.cast_one, add_mul] at hupper ⊢
      linarith
    · change Protocol.proposal_time S.E (S.hc.opening_slot r) ≤
        t + 3 * (Statements.Instantiation.constants S).period
      rw [hproposalTime]
      dsimp [r]
      have hlower := add_le_add_right hlow
        (3 * (Statements.Instantiation.constants S).period)
      norm_num [Nat.cast_add, Nat.cast_one, add_mul] at hlower ⊢
      linarith
    · change (∃ r' : Round, S.hc.opening_slot r = S.hc.opening_slot r') ∧ _
      refine ⟨⟨r, rfl⟩, ?_⟩
      intro k hk
      change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      simp
    · intro s' _ _ _
      change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      simp
  refine {
    execution := Proofs.genericExecutionValid_of_named S rho admissible_core
    partialSynchrony := Proofs.genericPartialSynchrony_of_named S rho synchrony
    gst := by simpa [Statements.Instantiation.env] using gst_zero.le
    committees := ?_
    belowThird := ?_
    allAwake := ?_
    recurrence := hrec
    gapBound := by norm_num [Statements.Instantiation.constants, S, cfg]
    longEnough := by
      norm_num [Statements.Instantiation.constants, Statements.Instantiation.finalityStartup,
        Setup.extraRounds, gap, extra, S, E, hc, cfg, rho, horizon,
        Protocol.vote_time, Env.t, slotStart, Setup.a, Protocol.HealConfig.a,
        Protocol.HealConfig.opening_slot, healingBoundaryTime] }
  · intro s
    simpa [Statements.Instantiation.interface, Statements.instance] using
      honest_committee_majority s
  · simpa [Statements.Instantiation.env, Statements.Generic.BelowOneThird,
      Execution.BelowOneThird] using below_one_third
  · intro v hv t ht hhor
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    subst v
    rfl

theorem generic_strong_live_sleepy_regime :
    Statements.Generic.StrongLiveSleepyRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) rho 0 3 := by
  have hfinal := generic_finality_regime
  have hperiod : 0 < (Statements.Instantiation.constants S).period :=
    Proofs.concretePeriod_pos S
  refine {
    toLiveSleepyRegime := {
      toSleepyRegime := {
        execution := hfinal.execution
        partialSynchrony := hfinal.partialSynchrony
        gst := hfinal.gst
        committees := hfinal.committees
        windows := ?_
        start := Statements.Generic.RecoveredBy.genesis }
      recurrence :=
        DecoupledConsensusModel.Proofs.Generic.MultiProposerRecurrence.toSingleProposerRecurrence
          (DecoupledConsensusModel.Proofs.Generic.StrongMultiProposerRecurrence.toMultiProposerRecurrence
            hfinal.recurrence hperiod)
          (by norm_num) (by simp [Statements.Instantiation.constants]) }
    strongRecurrence := hfinal.recurrence }
  · intro t ht hlag hhor
    classical
    have hL : 1 ≤ S.a 1 - S.a 0 := by
      exact Int.add_one_le_iff.mpr hperiod
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
/-! ## Closed finality safety, instantiated on this run -/

theorem finality_execution : FinalityExecution S rho :=
  FinalityExecution.of_executionValid admissible_core

theorem slashable_bound : SlashableBound S rho :=
  Proofs.HealingSurface.slashableBound_of_admissible_belowOneThird S
    admissible below_one_third

theorem finality_accountability_guarantee :
    WholeRunAccountableFinalitySafety S rho :=
  (Proofs.finalitySafety S).runAccountable rho finality_execution

theorem finality_agreement_guarantee : WholeRunFinalitySafety S rho :=
  (Proofs.finalitySafety S).runAgreement rho finality_execution slashable_bound

theorem genesis_in_run : NamedRun.blockInRun S rho NamedBlock.genesis := by
  refine ⟨NamedBlock.genesis, ?_, ?_⟩
  · right
    refine ⟨0, ?_, 0, ?_⟩
    · change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      simp
    simp [NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial]
  · simp [NamedBlock.Preceq, NamedBlock.preceq]

theorem genesis_finalized :
    NamedFinalizedAt S.E S.cfg NamedBlock.genesis Block.genesis 0 := by
  simp [NamedFinalizedAt, Protocol.derive_named,
    Protocol.ChainState.initial]

noncomputable def slotOneProposal : NamedBlock (Fin 2) :=
  Classical.choose (DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome S rho 1)

theorem slot_one_proposal_spec :
    Statements.Instantiation.proposedBlockAt S rho 1 = some slotOneProposal := by
  exact Classical.choose_spec (DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome S rho 1)

theorem slot_one_proposal_in_run :
    NamedRun.blockInRun S rho slotOneProposal := by
  apply DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_blockInRun_of_admissible
    S (Proofs.AdmissibleCore.ofParts admissible_core synchrony) 1 (by norm_num)
  · change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
    simp
  · norm_num [Protocol.proposal_time, S, E, horizon, rho, Env.t, slotStart]
  · exact slot_one_proposal_spec

theorem slot_one_proposal_finalized :
    NamedFinalizedAt S.E S.cfg slotOneProposal
      (Protocol.derive_named S.E S.cfg slotOneProposal).F
      (Protocol.derive_named S.E S.cfg slotOneProposal).h_F :=
  ⟨rfl, rfl⟩

theorem finality_on_genesis_and_slot_one_proposal :
    Block.compatible (Block.genesis : Block (Fin 2))
      (Protocol.derive_named S.E S.cfg slotOneProposal).F = true := by
  have h := finality_agreement_guarantee.1
    NamedBlock.genesis slotOneProposal Block.genesis
    (Protocol.derive_named S.E S.cfg slotOneProposal).F 0
    (Protocol.derive_named S.E S.cfg slotOneProposal).h_F
    genesis_in_run slot_one_proposal_in_run genesis_finalized
    slot_one_proposal_finalized
  exact h

theorem finality_inclusion_guard_active :
    ∃ s, (Statements.Instantiation.constants S).finalityStartup gap <
        (Statements.Instantiation.interface S).proposalTime s ∧
      (Statements.Instantiation.interface S).proposalTime s +
          (Statements.Instantiation.constants S).finalityDeadline gap ≤
        rho.horizon := by
  refine ⟨1966, ?_, ?_⟩
  · norm_num [Statements.Instantiation.constants,
      Statements.Instantiation.interface, Statements.Instantiation.finalityStartup,
      Statements.Instantiation.finalityDeadline, Setup.extraRounds, gap, extra, S, E, hc, cfg,
      Protocol.proposal_time, Env.t, slotStart, Protocol.HealConfig.opening_slot,
      Setup.a, Protocol.HealConfig.a, healingBoundaryTime, Protocol.vote_time]
  · norm_num [Statements.Instantiation.constants,
      Statements.Instantiation.interface, Statements.Instantiation.finalityStartup,
      Statements.Instantiation.finalityDeadline, Setup.extraRounds, gap, extra, S, E, hc, cfg,
      Protocol.proposal_time, Env.t, slotStart, Protocol.HealConfig.opening_slot,
      Setup.a, Protocol.HealConfig.a, healingBoundaryTime, Protocol.vote_time,
      horizon, rho]

theorem finality_growth_guard_active :
    (Statements.Instantiation.constants S).finalityStartup gap +
        (gap : Time) * (Statements.Instantiation.constants S).period +
        (Statements.Instantiation.constants S).finalityDeadline gap ≤
      rho.horizon := by
  change (Statements.Instantiation.constants S).finalityStartup gap +
      (gap : Time) * (Statements.Instantiation.constants S).period +
      (Statements.Instantiation.constants S).finalityDeadline gap ≤ horizon
  rw [horizon_formula]

/-! ## Explicit startup and deadline arithmetic -/

theorem startup_positive : 0 < startup := by
  simpa [startup] using Statements.finalityStartup_pos S gap extra

theorem startup_boundary_inside :
    healingBoundaryTime S startup ≤ rho.horizon := by
  change healingBoundaryTime S startup ≤ horizon
  rw [startup_value]
  norm_num [horizon, healingBoundaryTime, Protocol.vote_time, Env.t, slotStart,
    Protocol.HealConfig.opening_slot, S, E, hc, cfg]

theorem recurring_deadline_inside :
    S.a (startup + deadline) ≤ rho.horizon := by
  change S.a (startup + deadline) ≤ horizon
  rw [startup_value, deadline_value]
  norm_num [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
    healingBoundaryTime, Protocol.vote_time, Env.t, slotStart, horizon, S, E, hc,
    cfg]

theorem honest_proposal_deadline_inside :
    S.a (startup + deadline) ≤ rho.horizon :=
  recurring_deadline_inside



structure FinalityLivenessPrimitiveFacts : Prop where
  honestNonempty : rho.honest.Nonempty
  byzantineNonempty : (Finset.univ \ rho.honest).Nonempty
  schedule : ScheduleWellFormed S rho
  delivery : DeliveryWellFormed S rho
  roots : RootCollisionFree S rho
  authentic : Unforgeable S rho
  synchrony : Synchrony S rho
  committees : HonestCommittees S rho.honest
  totalWeight : S.E.W = 4
  honestWeight : S.E.electorate.weightOf rho.honest = 3
  byzantineWeight : S.E.electorate.weightOf (Finset.univ \ rho.honest) = 1
  belowThird : BelowOneThird S rho.honest
  honestAwake : ∀ r : Round, (S.node 0).awake r = true
  byzantineAsleep : ∀ r : Round, (S.node 1).awake r = false
  awakeWindowMajority : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest
      S.hc.η_SG r
  timeout : TimeoutDelayBound S extra
  recurrence : ProposerOpeningCarrierRecurrence S rho gap
  gapBound : gap + 2 ≤ S.cfg.K
  gstZero : S.E.t_GST = 0
  startupPositive : 0 < startup
  startupInHorizon : healingBoundaryTime S startup ≤ rho.horizon
  recurringDeadlineInHorizon : S.a (startup + deadline) ≤ rho.horizon
  honestProposalDeadlineInHorizon : S.a (startup + deadline) ≤ rho.horizon

theorem primitive_facts : FinalityLivenessPrimitiveFacts := by
  exact {
    honestNonempty := honest_nonempty
    byzantineNonempty := byzantine_nonempty
    schedule := schedule_well_formed
    delivery := delivery_well_formed
    roots := root_collision_free
    authentic := authentic
    synchrony := synchrony
    committees := honest_committee_majority
    totalWeight := total_weight_eq
    honestWeight := honest_weight_eq
    byzantineWeight := byzantine_weight_eq
    belowThird := below_one_third
    honestAwake := honest_awake
    byzantineAsleep := byzantine_asleep
    awakeWindowMajority := awake_window_majority
    timeout := timeout_bound
    recurrence := recurrence
    gapBound := gap_bound
    gstZero := gst_zero
    startupPositive := startup_positive
    startupInHorizon := startup_boundary_inside
    recurringDeadlineInHorizon := recurring_deadline_inside
    honestProposalDeadlineInHorizon := honest_proposal_deadline_inside }

theorem public_finality_liveness_on_setup :
    Statements.FinalizedChainGrowth S ∧
      Statements.HonestProposalFinalization S :=
  ⟨Proofs.finalizedChainGrowth S, Proofs.honestProposalFinalization S⟩

theorem finalized_chain_growth_activated : Statements.FinalizedChainGrowth S :=
  Proofs.finalizedChainGrowth S

theorem honest_proposal_finalization_activated :
    Statements.HonestProposalFinalization S :=
  Proofs.honestProposalFinalization S

theorem finalized_chain_growth_gst_zero_contract :
    ∀ rho', StrongFinalityRun S rho' gap → S.E.t_GST = 0 →
      healingBoundaryTime S (finalityStartup S gap extra) ≤ rho'.horizon →
      ∃ q, q ≤ finalityStartup S gap extra ∧
        RecurringFinalityFrom S rho' q (finalityDeadline S gap extra) := by
  exact finalized_chain_growth_activated.gstZero extra timeout_bound gap

theorem honest_proposal_finalization_gst_zero_contract :
    ∀ rho', StrongFinalityRun S rho' gap → S.E.t_GST = 0 →
      healingBoundaryTime S (finalityStartup S gap extra) ≤ rho'.horizon →
      ∃ q, q ≤ finalityStartup S gap extra ∧
        HonestProposalFinalityFrom S rho' q (finalityDeadline S gap extra) := by
  exact honest_proposal_finalization_activated.gstZero extra timeout_bound gap

theorem finality_liveness_activated :
    StrongFinalityRun S rho gap ∧ TimeoutDelayBound S extra ∧
      S.E.t_GST = 0 ∧ 0 < startup ∧
      healingBoundaryTime S startup ≤ rho.horizon ∧
      S.a (startup + deadline) ≤ rho.horizon ∧
      Statements.FinalizedChainGrowth S ∧
      Statements.HonestProposalFinalization S := by
  exact ⟨strong_finality_run, timeout_bound, gst_zero, startup_positive,
    startup_boundary_inside, recurring_deadline_inside,
    finalized_chain_growth_activated, honest_proposal_finalization_activated⟩

#print axioms schedule_well_formed
#print axioms delivery_well_formed
#print axioms root_collision_free
#print axioms originState
#print axioms authentic
#print axioms synchrony
#print axioms admissible_core
#print axioms admissible
#print axioms strong_finality_run
#print axioms primitive_facts
#print axioms finality_accountability_guarantee
#print axioms finality_agreement_guarantee
#print axioms finality_on_genesis_and_slot_one_proposal
#print axioms finality_inclusion_guard_active
#print axioms finality_growth_guard_active
#print axioms finalized_chain_growth_activated
#print axioms honest_proposal_finalization_activated
#print axioms finalized_chain_growth_gst_zero_contract
#print axioms honest_proposal_finalization_gst_zero_contract
#print axioms finality_liveness_activated

end Witnesses.FinalityLiveness
end DecoupledConsensusModel

end
