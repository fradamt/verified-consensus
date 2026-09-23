module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel
public import DecoupledConsensusProofs.ReviewTheorem
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
namespace Witnesses.StrongRecovery

open Internal Execution

def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 1
  t_GST_nonneg := by norm_num
  proposer := fun _ => 0
  committees := ⟨fun _ => {0}⟩
  electorate :=
    { weight := fun v => if v = 0 then 3 else 1
      weight_pos := by intro v; fin_cases v <;> simp }

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

def nd : Protocol.Node (Fin 2) where
  val_index := 0
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true

def S : Setup (Fin 2) where
  E := E
  hc := hc
  cfg := cfg
  node := fun v => { nd with val_index := v }
  node_val_index := by intro v; rfl
  timeout_rounds := by decide
  committee_nonempty := by
    intro s
    change ({0} : Finset (Fin 2)).Nonempty
    simp
  outage_window := by decide

def tickEvents : Nat → Nat → List (Event (Fin 2))
  | _, 0 => []
  | k, n + 1 => Event.tick 0 (k : Time) :: tickEvents (k + 1) n

def events (N : Nat) : List (Event (Fin 2)) :=
  tickEvents 0 (N + 1)

def rho (N : Nat) : Run (Fin 2) :=
  ⟨{0}, (N : Time), events N⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/- These diagnostic evaluations run in plain Lean scripts, not in a module:
#eval (events 30).length
#eval (NamedRun.stateBefore S (rho 30) 31 0).st.core.h_max
#eval (NamedRun.stateBefore S (rho 30) 31 0).st.core.T.card
-/

def rGST : Round := 1
def gap : Round := 2
def extra : Nat := 0
def phaseLag : Round := (4 * gap + 12 + 2 * extra) + 3 * gap + 10 + 2 * extra

def seed : Run (Fin 2) := rho 30

noncomputable def earlyHeight : Height := Internal.honestHMaxBeforeIndex S seed 31

noncomputable def prefixEnd : Round :=
  rGST + 1 + (1 + (S.cfg.D + S.cfg.K + 5) * phaseLag) +
    2 * phaseLag + max (1 + S.hc.η_SG) (gap + 3)

noncomputable def horizonTime : Time := S.a (prefixEnd + gap)

noncomputable def eventCount : Nat := Int.toNat horizonTime

class TickTrace where
  horizonTime : Time
  eventCount : Nat
  horizonTime_coe : (eventCount : Time) = horizonTime
  eventCount_ge_30 : 30 ≤ eventCount

noncomputable def run [trace : TickTrace] : Run (Fin 2) :=
  rho trace.eventCount

theorem phaseLag_value : phaseLag = 36 := by
  norm_num [phaseLag, gap, extra]

theorem prefixEnd_ge_30 : 30 ≤ prefixEnd := by
  unfold prefixEnd
  simp [rGST, gap, extra, phaseLag, S, hc, cfg]

theorem horizonTime_nonneg : 0 ≤ horizonTime := by
  exact _root_.DecoupledConsensusModel.Proofs.HealingLemmas.a_nonneg S (prefixEnd + gap)

theorem horizonTime_coe : (eventCount : Time) = horizonTime := by
  simp only [eventCount]
  exact Int.toNat_of_nonneg horizonTime_nonneg

theorem eventCount_ge_30 : 30 ≤ eventCount := by
  have htime : (30 : Time) ≤ horizonTime := by
    have hround : 2 ≤ prefixEnd + gap := by
      have hp : 30 ≤ prefixEnd := prefixEnd_ge_30
      simpa [gap] using (Nat.le_trans (by norm_num : 1 ≤ 30) hp)
    have hmono : S.a 2 ≤ S.a (prefixEnd + gap) :=
      _root_.DecoupledConsensusModel.Proofs.Assembly.a_mono S hround
    have ha2 : (30 : Time) ≤ S.a 2 := by
      norm_num [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
        slotStart, S, hc, cfg, E]
    exact ha2.trans hmono
  have htime' : (30 : Time) ≤ (eventCount : Time) := by
    rw [horizonTime_coe]
    exact htime
  exact_mod_cast htime'

noncomputable def continuationHorizonTime : Time :=
  healingBoundaryTime S (prefixEnd + gap)

noncomputable def continuationEventCount : Nat := eventCount + 3

theorem continuationHorizonTime_formula :
    continuationHorizonTime = horizonTime + 3 := by
  norm_num [continuationHorizonTime, horizonTime, healingBoundaryTime,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
    Protocol.vote_time, Env.t, slotStart, S, E, hc, cfg]
  ring

theorem continuationHorizonTime_nonneg : 0 ≤ continuationHorizonTime := by
  exact (horizonTime_nonneg.trans
    (Proofs.a_le_healingBoundaryTime S (prefixEnd + gap)))

theorem continuationHorizonTime_coe :
    (continuationEventCount : Time) = continuationHorizonTime := by
  rw [continuationEventCount, Nat.cast_add, horizonTime_coe]
  exact continuationHorizonTime_formula.symm

theorem continuationEventCount_ge_30 : 30 ≤ continuationEventCount := by
  unfold continuationEventCount
  have h := eventCount_ge_30
  omega

noncomputable def sourceTrace : TickTrace := {
  horizonTime := horizonTime
  eventCount := eventCount
  horizonTime_coe := horizonTime_coe
  eventCount_ge_30 := eventCount_ge_30 }

noncomputable def continuationTrace : TickTrace := {
  horizonTime := continuationHorizonTime
  eventCount := continuationEventCount
  horizonTime_coe := continuationHorizonTime_coe
  eventCount_ge_30 := continuationEventCount_ge_30 }

noncomputable def sourceRun : Run (Fin 2) := @run sourceTrace

noncomputable def continuationRun : Run (Fin 2) := @run continuationTrace

section Trace

variable [trace : TickTrace]

theorem tickEvents_length (start count : Nat) :
    (tickEvents start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [tickEvents, ih]

theorem tickEvents_append (start a b : Nat) :
    tickEvents start (a + b) = tickEvents start a ++ tickEvents (start + a) b := by
  induction a generalizing start with
  | zero => simp [tickEvents]
  | succ a ih =>
      have hab : a + 1 + b = (a + b) + 1 := by omega
      rw [hab]
      simp only [tickEvents, List.cons_append]
      rw [ih (start := start + 1)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem tickEvents_take (start count k : Nat) (hk : k ≤ count) :
    (tickEvents start count).take k = tickEvents start k := by
  induction k generalizing start count with
  | zero => rfl
  | succ k ih =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [tickEvents, List.take]
          rw [ih (start := start + 1) (count := count)
            (Nat.le_of_succ_le_succ hk)]

theorem tickEvents_time_le (start count : Nat) (hbound : start + count ≤ 31) :
    ∀ e ∈ tickEvents start count, e.time ≤ (30 : Time) := by
  revert hbound
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      intro hbound
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · norm_num
        have hs : start ≤ 30 := by omega
        change (start : Time) ≤ (30 : Time)
        exact_mod_cast hs
      · have hb : (start + 1) + count ≤ 31 := by omega
        exact ih (start := start + 1) hb e he

theorem tickEvents_time_gt (start count : Nat) (hstart : 30 < start) :
    ∀ e ∈ tickEvents start count, ¬ e.time ≤ (30 : Time) := by
  revert hstart
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      intro hstart
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · norm_num
        have hs : (30 : Nat) < start := hstart
        have hs' : (30 : Time) < (start : Time) := by exact_mod_cast hs
        change (30 : Time) < (start : Time)
        exact hs'
      · exact ih (start := start + 1) (by omega) e he

theorem tickEvents_filter_initial (N : Nat) (hN : 30 ≤ N) :
    ((tickEvents 0 (N + 1)).filter
      (fun e => decide (e.time ≤ (30 : Time)))).length = 31 := by
  have hsplit : N + 1 = 31 + (N - 30) := by omega
  rw [hsplit, tickEvents_append, List.filter_append]
  have hfirst :
      (tickEvents 0 31).filter
        (fun e => decide (e.time ≤ (30 : Time))) = tickEvents 0 31 := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    exact tickEvents_time_le 0 31 (by omega) e he
  have htail :
      (tickEvents 31 (N - 30)).filter
        (fun e => decide (e.time ≤ (30 : Time))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp only [decide_eq_true_eq]
    exact tickEvents_time_gt 31 (N - 30) (by omega) e he
  rw [hfirst, htail]
  simp [tickEvents_length]

theorem initial_event_count :
    (run.events.filter (fun e => decide (e.time ≤ S.a (rGST + 1)))).length = 31 := by
  change ((tickEvents 0 (trace.eventCount + 1)).filter
    (fun e => decide (e.time ≤ (30 : Time)))).length = 31
  exact tickEvents_filter_initial trace.eventCount trace.eventCount_ge_30

theorem run_prefix_eq_seed : run.events.take 31 = seed.events.take 31 := by
  change (tickEvents 0 (trace.eventCount + 1)).take 31 = (tickEvents 0 31).take 31
  rw [tickEvents_take 0 (trace.eventCount + 1) 31
    (Nat.succ_le_succ trace.eventCount_ge_30)]
  rw [tickEvents_take 0 31 31 le_rfl]

theorem stateBefore_prefix :
    Run.stateBefore S run 31 = Run.stateBefore S seed 31 := by
  change (run.events.take 31).foldl (NamedWorld.step S) NamedWorld.init =
    (seed.events.take 31).foldl (NamedWorld.step S) NamedWorld.init
  rw [run_prefix_eq_seed]

theorem initial_height :
    Internal.honestHMaxBeforeIndex S run 31 = earlyHeight := by
  unfold Internal.honestHMaxBeforeIndex earlyHeight
  change ({0} : Finset (Fin 2)).sup
      (fun v => (Run.stateBefore S run 31 v).st.h_max) =
    ({0} : Finset (Fin 2)).sup
      (fun v => (Run.stateBefore S seed 31 v).st.h_max)
  rw [Finset.sup_singleton, Finset.sup_singleton]
  rw [stateBefore_prefix]

theorem boundedPhaseStart :
    Internal.BoundedPhaseStart S run rGST gap extra prefixEnd := by
  unfold Internal.BoundedPhaseStart
  dsimp
  rfl

theorem tickEvents_time_ge (start count : Nat) :
    ∀ e ∈ tickEvents start count, (start : Time) ≤ e.time := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · have h := ih (start := start + 1) e he
        have hs : (start : Nat) ≤ start + 1 := Nat.le_succ _
        exact le_trans (by exact_mod_cast hs) h

theorem tickEvents_time_lt (start count : Nat) :
    ∀ e ∈ tickEvents start count, e.time < (start + count : Time) := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · change (start : Time) < (start + (count + 1) : Time)
        exact_mod_cast (by omega : start < start + (count + 1))
      · have h := ih (start := start + 1) e he
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h

theorem tickEvents_is_tick (start count : Nat) :
    ∀ e ∈ tickEvents start count, ∃ k : Nat, e = Event.tick 0 (k : Time) := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      intro e he
      simp only [tickEvents, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨start, rfl⟩
      · exact ih (start := start + 1) e he

theorem tickEvents_mem (start count k : Nat) (hstart : start ≤ k)
    (hlt : k < start + count) :
    Event.tick 0 (k : Time) ∈ tickEvents start count := by
  induction count generalizing start k with
  | zero => omega
  | succ count ih =>
      simp only [tickEvents, List.mem_cons]
      by_cases hk : k = start
      · subst k
        simp
      · right
        apply ih (start := start + 1) (k := k)
        · exact Nat.succ_le_of_lt (lt_of_le_of_ne hstart (Ne.symm hk))
        · omega

theorem tickEvents_mem_zero (N k : Nat) (hk : k ≤ N) :
    Event.tick 0 (k : Time) ∈ tickEvents 0 (N + 1) := by
  apply tickEvents_mem 0 (N + 1) k (Nat.zero_le _)
  omega

theorem event_at_tick {i : Nat} {e : Event (Fin 2)}
    (he : run.events[i]? = some e) :
    ∃ k : Nat, e = Event.tick 0 (k : Time) := by
  have hm : e ∈ run.events := List.mem_of_getElem? he
  have hm' : e ∈ tickEvents 0 (trace.eventCount + 1) := by
    simpa [run, rho] using hm
  exact tickEvents_is_tick 0 (trace.eventCount + 1) e hm'

theorem tickEvents_pairwise (start count : Nat) :
    (tickEvents start count).Pairwise
      (fun e f => NamedEvent.key e ≤ NamedEvent.key f) := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      simp only [tickEvents, List.pairwise_cons]
      refine ⟨?_, ih (start := start + 1)⟩
      intro e he
      obtain ⟨k, rfl⟩ := tickEvents_is_tick (start + 1) count e he
      have hsk : start < k := by
        have h := tickEvents_time_ge (start + 1) count
          (Event.tick 0 (k : Time)) he
        change (start + 1 : Time) ≤ (k : Time) at h
        have hsk' : start < k := by exact_mod_cast h
        exact hsk'
      change toLex ((start : Time), 0) ≤ toLex ((k : Time), 0)
      have hsk' : (start : Time) < (k : Time) := by exact_mod_cast hsk
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hsk')

theorem tickEvents_nodup (start count : Nat) :
    (tickEvents start count).Nodup := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      simp only [tickEvents, List.nodup_cons]
      constructor
      · intro he
        obtain ⟨k, hkEq⟩ := tickEvents_is_tick (start + 1) count _ he
        have he_k : Event.tick 0 (k : Time) ∈ tickEvents (start + 1) count := by
          simpa [hkEq] using he
        have hsk : start < k := by
          have h := tickEvents_time_ge (start + 1) count
            (Event.tick 0 (k : Time)) he_k
          change (start + 1 : Time) ≤ (k : Time) at h
          have hsk' : start + 1 ≤ k := by exact_mod_cast h
          omega
        have htime : (start : Time) = (k : Time) := by
          injection hkEq with _ htime
        have : start = k := by exact_mod_cast htime
        exact (Nat.ne_of_lt hsk) this
      · exact ih (start := start + 1)

theorem scheduleWellFormed_count (N : Nat) : ScheduleWellFormed S (rho N) where
  horizon_nonneg := by
    change 0 ≤ (N : Time)
    exact_mod_cast Nat.zero_le N
  sorted := by
    change (tickEvents 0 (N + 1)).Pairwise
      (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
    exact tickEvents_pairwise 0 (N + 1)
  nodup := by
    change (tickEvents 0 (N + 1)).Nodup
    exact tickEvents_nodup 0 (N + 1)
  in_horizon := by
    intro e he
    obtain ⟨k, hk⟩ := tickEvents_is_tick 0 (N + 1) e he
    have he_k : Event.tick 0 (k : Time) ∈ tickEvents 0 (N + 1) := by
      simpa [hk] using he
    have hlt := tickEvents_time_lt 0 (N + 1)
      (Event.tick 0 (k : Time)) he_k
    have hkN : k ≤ N := by
      have hlt' : (k : Time) < (N + 1 : Time) := by
        simpa [NamedEvent.time] using hlt
      have hltN : k < N + 1 := by exact_mod_cast hlt'
      exact Nat.le_of_lt_succ hltN
    constructor
    · rw [hk]
      change (0 : Time) ≤ (k : Time)
      exact_mod_cast (Nat.zero_le k)
    · rw [hk]
      change (k : Time) ≤ (N : Time)
      exact_mod_cast hkN
  honest_only := by
    intro e he
    have hev : e.node = 0 := by
      obtain ⟨k, rfl⟩ := tickEvents_is_tick 0 (N + 1) e he
      rfl
    simpa [rho] using hev
  tick_public := by
    intro v t hmem
    obtain ⟨k, hk⟩ := tickEvents_is_tick 0 (N + 1)
      (Event.tick v t) hmem
    have hm : t = (k : Time) := by
      simpa using congrArg NamedEvent.time hk
    refine ⟨k, ?_⟩
    rw [hm]
    norm_num [S, E]
  tick_total := by
    rintro v hv t ⟨k, ht⟩ hnonneg hle
    have hv0 : v = 0 := by simpa [rho] using hv
    subst v
    have ht' : t = (k : Time) := by simpa [S, E] using ht
    have hk0 : (0 : Nat) ≤ k := by
      have : (0 : Time) ≤ (k : Time) := by simpa [ht', NamedEvent.time] using hnonneg
      exact_mod_cast this
    have hkN : k ≤ N := by
      have : (k : Time) ≤ (N : Time) := by simpa [ht', rho, NamedEvent.time] using hle
      exact_mod_cast this
    have hmem : Event.tick 0 (k : Time) ∈
        tickEvents 0 (N + 1) :=
      tickEvents_mem_zero N k hkN
    simpa [rho, ht'] using hmem

theorem run_eq_rho_eventCount : run = rho trace.eventCount := by
  rfl

theorem source_continuation_agrees :
    AgreesUntil sourceRun continuationRun (S.a (prefixEnd + gap)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    simpa [sourceRun, continuationRun, run, sourceTrace, continuationTrace, rho] using hv
  · intro v hv
    have hv0 : v = 0 := by
      change v ∈ ({0} : Finset (Fin 2)) at hv
      simpa using hv
    subst v
    have hcut : S.a (prefixEnd + gap) = (eventCount : Time) := by
      simpa [horizonTime] using horizonTime_coe.symm
    change
      (tickEvents 0 (continuationEventCount + 1)).filter
          (fun e => decide (e.node = 0 ∧ e.time < S.a (prefixEnd + gap))) =
        (tickEvents 0 (eventCount + 1)).filter
          (fun e => decide (e.node = 0 ∧ e.time < S.a (prefixEnd + gap)))
    rw [continuationEventCount, show eventCount + 3 + 1 = (eventCount + 1) + 3 by omega,
      tickEvents_append, List.filter_append]
    have htail :
        (tickEvents (eventCount + 1) 3).filter
            (fun e => decide (e.node = 0 ∧ e.time < S.a (prefixEnd + gap))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      obtain ⟨k, rfl⟩ := tickEvents_is_tick (eventCount + 1) 3 e he
      have hge : (eventCount + 1 : Time) ≤ (k : Time) := by
        simpa only [NamedEvent.time] using
          (tickEvents_time_ge (eventCount + 1) 3
            (Event.tick 0 (k : Time)) he)
      have hnot : ¬ (k : Time) < (eventCount : Time) := by
        have hstep : (eventCount : Time) ≤ (eventCount + 1 : Time) := by
          exact_mod_cast (Nat.le_succ eventCount)
        exact not_lt_of_ge (by
          calc
            (eventCount : Time) ≤ (eventCount + 1 : Time) := hstep
            _ ≤ (k : Time) := hge)
      rw [hcut]
      simp only [NamedEvent.node, NamedEvent.time, decide_eq_true_eq]
      intro h
      exact hnot h.2
    simp only [Nat.zero_add]
    rw [htail, List.append_nil]

theorem scheduleWellFormed : ScheduleWellFormed S run := by
  rw [run_eq_rho_eventCount]
  exact scheduleWellFormed_count trace.eventCount

theorem no_delivery_at_index {i : Nat} {v : Fin 2} {o : Object (Fin 2)} {t : Time}
    (he : run.events[i]? = some (.deliver v o t)) : False := by
  obtain ⟨k, hk⟩ := event_at_tick he
  have hbad : Event.deliver v o t = Event.tick 0 (k : Time) := hk
  cases hbad

theorem deliveryWellFormed : DeliveryWellFormed S run where
  wire := by intro i v o t h; exact False.elim (no_delivery_at_index h)
  deps := by intro i v o t h; exact False.elim (no_delivery_at_index h)
  fresh := by intro i v o t h; exact False.elim (no_delivery_at_index h)

theorem honest_zero : (0 : Fin 2) ∈ run.honest := by
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem honest_mem_eq_zero {v : Fin 2} (hv : v ∈ run.honest) : v = 0 := by
  change v ∈ ({0} : Finset (Fin 2)) at hv
  simpa using hv

theorem byzantine_one : (1 : Fin 2) ∉ run.honest := by
  change (1 : Fin 2) ∉ ({0} : Finset (Fin 2))
  simp

theorem honest_nonempty : run.honest.Nonempty := ⟨0, honest_zero⟩

theorem byzantine_nonempty : (Finset.univ \ run.honest).Nonempty := by
  refine ⟨1, ?_⟩
  change (1 : Fin 2) ∈ Finset.univ \ ({0} : Finset (Fin 2))
  simp

theorem honestCommittees : HonestCommittees S run.honest := by
  intro s
  change ({0} : Finset (Fin 2)).card <
    2 * (({0} : Finset (Fin 2)) ∩ ({0} : Finset (Fin 2))).card
  norm_num

theorem belowOneThird : BelowOneThird S run.honest := by
  change 3 * Electorate.weightOf E.electorate (Finset.univ \ ({0} : Finset (Fin 2))) <
    Electorate.totalWeight E.electorate
  norm_num [E, Electorate.weightOf, Electorate.totalWeight]
  decide

theorem honestWeightMajority : HonestWeightMajority S run.honest := by
  change Electorate.weightOf E.electorate (Finset.univ \ ({0} : Finset (Fin 2))) <
    Electorate.weightOf E.electorate ({0} : Finset (Fin 2))
  norm_num [E, Electorate.weightOf]
  decide

theorem timeoutDelayBound : TimeoutDelayBound S extra := by
  norm_num [TimeoutDelayBound, S, hc, cfg, extra]

theorem postGST : S.E.t_GST ≤ S.a rGST := by
  norm_num [S, E, hc, rGST, Setup.a, Protocol.HealConfig.a,
    Protocol.HealConfig.opening_slot, slotStart]

theorem awake_all : ∀ v ∈ run.honest, ∀ r : Round, S.a r ≤ run.horizon →
    (S.node v).awake r = true := by
  intro v hv r hhor
  rfl

theorem proposerCarrierAt (r : Round) :
    ProposerCarrierAt S run r := by
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
    (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
      (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem proposerRecurrence : MultiProposerRecurrence S run gap := by
  intro r
  exact ⟨r, le_rfl, by simp [gap], proposerCarrierAt r⟩

theorem generic_proposer_recurrence :
    Statements.Generic.MultiProposerRecurrence
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S) sourceRun gap := by
  intro t ht
  let L : Time := S.a 1 - S.a 0
  let q : Nat := Int.toNat (t / L)
  let r : Round := q + 1
  have hL : 0 < L := by
    exact Proofs.concretePeriod_pos S
  have hq : 0 ≤ t / L := Int.ediv_nonneg ht hL.le
  have hq' : (q : Time) = t / L := by
    dsimp [q]
    exact Int.toNat_of_nonneg hq
  have hlow : (q : Time) * L ≤ t := by
    rw [hq']
    exact Int.ediv_mul_le _ (ne_of_gt hL)
  have hupp : t < ((q : Time) + 1) * L := by
    have h := Int.lt_ediv_add_one_mul_self t hL
    simpa [hq'] using h
  have hproposal : Protocol.proposal_time S.E (S.hc.opening_slot r) =
      (r : Time) * L := by
    simpa [r, L] using Proofs.openingProposalTime_eq_period S r
  refine ⟨S.hc.opening_slot r, ?_, ?_, ?_⟩
  · change t < Protocol.proposal_time S.E (S.hc.opening_slot r)
    rw [hproposal]
    have hr : (r : Time) = (q : Time) + 1 := by
      simp [r]
    rw [hr]
    exact hupp
  · change Protocol.proposal_time S.E (S.hc.opening_slot r) ≤ t + gap *
      (Statements.Instantiation.constants S).period
    rw [hproposal]
    have hr : (r : Time) = (q : Time) + 1 := by
      simp [r]
    rw [hr]
    simp [gap, L, Statements.Instantiation.constants]
    nlinarith [hlow, hL.le]
  · change (∃ r' : Round, S.hc.opening_slot r = S.hc.opening_slot r') ∧
      ∀ k < 3, S.E.proposer (S.hc.opening_slot r + k) ∈ sourceRun.honest
    refine ⟨⟨r, rfl⟩, ?_⟩
    intro k hk
    change (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
    simp

theorem proposerOpeningCarrierAt (r : Round) :
    ProposerOpeningCarrierAt S run r := by
  change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
    (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
      (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
        (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
          (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
  simp

theorem proposerOpeningCarrierRecurrence :
    ProposerOpeningCarrierRecurrence S run gap := by
  intro k
  exact ⟨k + 2, le_rfl, by simp [gap], proposerOpeningCarrierAt (k + 2)⟩

theorem self_handles_of_emission {i : Nat} {o : Object (Fin 2)} {t : Time}
    (hi : run.events[i]? = some (.tick 0 t))
    (ho : o ∈ NamedRun.emittedAt S run i 0 t) :
    NamedRun.actualHandlesAt S run i 0 o t := by
  refine ⟨?_, ⟨.tick 0 t, hi, rfl, rfl⟩⟩
  cases o with
  | block B => exact Or.inl ⟨t, hi, ho⟩
  | gfVote u => exact Or.inl (Or.inl ⟨t, hi, ho⟩)
  | attest a => exact Or.inl (Or.inl ⟨t, hi, ho⟩)

theorem sync_deadline_strict (t : Time) :
    t < max t S.E.t_GST + S.E.Δ := by
  change t < max t 1 + 1
  by_cases h : t ≤ 1
  · rw [max_eq_right h]
    exact lt_of_le_of_lt h (by norm_num)
  · rw [max_eq_left (le_of_not_ge h)]
    exact lt_add_of_pos_right _ (by norm_num)

theorem synchrony : Synchrony S run where
  broadcast := by
    intro v hv o t hemit w hw hdeadline _hguard
    have hv0 : v = 0 := honest_mem_eq_zero hv
    have hw0 : w = 0 := honest_mem_eq_zero hw
    subst v
    subst w
    obtain ⟨i, hi, ho⟩ := hemit
    refine ⟨t, le_rfl, ?_, i, self_handles_of_emission hi ho⟩
    exact sync_deadline_strict t
  relay_block := by
    intro v hv i B t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := honest_mem_eq_zero hv
    have hw0 : w = 0 := honest_mem_eq_zero hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩

  relay_gf_vote := by
    intro v hv i u t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := honest_mem_eq_zero hv
    have hw0 : w = 0 := honest_mem_eq_zero hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩
  relay_attest := by
    intro v hv i a t hacc w hw hmissing hdeadline _hguard
    have hv0 : v = 0 := honest_mem_eq_zero hv
    have hw0 : w = 0 := honest_mem_eq_zero hw
    subst v
    subst w
    exact ⟨t, le_rfl, sync_deadline_strict t, i, hacc.1⟩



def EmitBefore (i : Nat) (o : Object (Fin 2)) : Prop :=
  ∃ j : Nat, j < i ∧ ∃ t : Time,
    run.events[j]? = some (.tick 0 t) ∧
      o ∈ NamedRun.emittedAt S run j 0 t

structure OriginState (i : Nat) : Prop where
  body : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S run i 0).st.bodies →
      B = NamedBlock.genesis ∨ EmitBefore i (.block B)
  body_gf : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S run i 0).st.bodies →
      ∀ u : GoldfishVote (Fin 2), u ∈ B.gf_votes →
        EmitBefore i (.gfVote u)
  body_row : ∀ B : NamedBlock (Fin 2),
    B ∈ (NamedRun.stateBefore S run i 0).st.bodies →
      ∀ a : NamedAttestation (Fin 2), a ∈ B.attestations →
        EmitBefore i (.attest a)
  gf : ∀ k : Slot, ∀ u : GoldfishVote (Fin 2),
    u ∈ (NamedRun.stateBefore S run i 0).st.core.gf_votes k →
      EmitBefore i (.gfVote u)
  row : ∀ k : Round, ∀ a : NamedAttestation (Fin 2),
    a ∈ (NamedRun.stateBefore S run i 0).st.sg_rows k →
      EmitBefore i (.attest a)

theorem emitBefore_mono {i j : Nat} (hij : i ≤ j) {o : Object (Fin 2)}
    (h : EmitBefore i o) : EmitBefore j o := by
  rcases h with ⟨k, hki, t, he, ho⟩
  exact ⟨k, hki.trans_le hij, t, he, ho⟩

theorem emitBefore_emits {i : Nat} {o : Object (Fin 2)}
    (h : EmitBefore i o) : ∃ t : Time, NamedRun.emits S run 0 o t := by
  rcases h with ⟨j, -, t, he, ho⟩
  exact ⟨t, ⟨j, he, ho⟩⟩

theorem orderedBodies_mem {st : Protocol.NamedStore (Fin 2)} {B : NamedBlock (Fin 2)}
    (hB : B ∈ Protocol.NamedProposalRows.orderedBodies st) : B ∈ st.bodies := by
  unfold Protocol.NamedProposalRows.orderedBodies at hB
  simp only [List.mem_filterMap] at hB
  obtain ⟨root, hroot, hfind⟩ := hB
  exact Proofs.Engine.pickUnique?_mem hfind

theorem emitted_block_fields {i : Nat} {t : Time} {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S run i 0 t) :
    B.slot = (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).st.core.s ∧
      B.root = (S.node 0).new_root
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.s ∧
      B.proposer? = some 0 := by
  have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S run i 0) t hB
  have hproposal :
      Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hshape
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st with
    | none => simp [hp] at hshape
    | some C =>
      simp [hp] at hshape ⊢
      exact hshape.2
  have hp := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st B hproposal
  rcases hp with ⟨-, -, hslot, hroot, -, -, -, hprop⟩
  have hfields := Proofs.DutyInputDefaults.proposal_input_fields
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).cache)
    S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st.core.toHealing
  exact ⟨hslot.trans hfields.1,
    hroot.trans hfields.2.1,
    by
      have hpropeq : B.proposer? = some (S.node 0).val_index :=
        hprop.trans (congrArg some hfields.2.2.1)
      simpa [S, E] using hpropeq⟩

theorem emitted_block_gf_origin {i : Nat} {t : Time} {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S run i 0 t)
    (hstate : OriginState i) {u : GoldfishVote (Fin 2)}
    (hu : u ∈ B.gf_votes) : EmitBefore i (.gfVote u) := by
  have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S run i 0) t hB
  have hproposal :
      Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hshape
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st with
    | none => simp [hp] at hshape
    | some C =>
      simp [hp] at hshape ⊢
      exact hshape.2
  have hp := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st B hproposal
  rcases hp with ⟨-, -, -, -, hgf, -, -, -⟩
  have hfields := Proofs.DutyInputDefaults.proposal_input_fields
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).cache)
    S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st.core.toHealing
  have hgf' : B.gf_votes =
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).st.core.gf_votes
        ((NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.s - 1) := by
    calc
      B.gf_votes = (Protocol.proposal_input_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.toHealing).gf_votes := hgf
      _ = Protocol.proposer_view
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.toHealing.toFG.toSG.toGoldfishStore
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.toHealing.s :=
          hfields.2.2.2.1
      _ = (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.gf_votes
          ((NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).st.core.s - 1) := by rfl
  have hu' : u ∈ (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st.core.gf_votes
      ((NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).st.core.s - 1) := by
    rw [← hgf']
    exact hu
  exact hstate.gf _ _ (by simpa [NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using hu')

theorem emitted_block_row_origin {i : Nat} {t : Time} {B : NamedBlock (Fin 2)}
    (hB : Object.block B ∈ NamedRun.emittedAt S run i 0 t)
    (hstate : OriginState i) {a : NamedAttestation (Fin 2)}
    (ha : a ∈ B.attestations) : EmitBefore i (.attest a) := by
  have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S 0
    (NamedRun.stateBefore S run i 0) t hB
  have hproposal :
      Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st = some B := by
    unfold Protocol.NamedDuties.propose_block_with at hshape
    cases hp : Protocol.NamedActions.proposal_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S run i 0) t).cache)
        .poolAndCarried S.E S.hc (S.node 0)
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st with
    | none => simp [hp] at hshape
    | some C =>
      simp [hp] at hshape ⊢
      exact hshape.2
  have hp := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).cache)
    .poolAndCarried S.E S.hc (S.node 0)
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBefore S run i 0) t).st B hproposal
  rcases hp with ⟨-, -, -, -, -, -, hrows, -⟩
  have hsel : a ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).st := by
    exact (Proofs.NamedProposalRows.mem_proposalRows B.parent _ a (hrows ▸ ha)).1
  have hsource : a ∈ Protocol.NamedProposalRows.poolRows S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S run i 0) t).st ∨
      a ∈ Protocol.NamedProposalRows.carriedRows S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st := by
    simpa [Protocol.NamedProposalRows.select] using hsel
  rcases hsource with hpool | hcarried
  · have hprocessed : a ∈ Protocol.NamedProposalRows.processedRows S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st :=
      (List.mem_filter.mp hpool).1
    unfold Protocol.NamedProposalRows.processedRows at hprocessed
    obtain ⟨r, hr, hrow⟩ := List.mem_flatMap.mp hprocessed
    exact hstate.row r a (by simpa [NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hrow)
  · unfold Protocol.NamedProposalRows.carriedRows at hcarried
    obtain ⟨C, hC, hrow⟩ := List.mem_flatMap.mp hcarried
    split at hrow
    · have hrow' := (List.mem_filter.mp hrow).1
      have hC' : C ∈ (NamedRun.stateBefore S run i 0).st.bodies := by
        simpa [NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using orderedBodies_mem hC
      exact hstate.body_row C hC' a hrow'
    · simp at hrow

theorem originState_tick {i k : Nat}
    (he : run.events[i]? = some (.tick 0 (k : Time)))
    (hstate : OriginState i) : OriginState (i + 1) := by
  let n := NamedRun.stateBefore S run i 0
  let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing (k : Time) n.cache
  let gc := DecoupledConsensusModel.Protocol.frameContract c
  let out := Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node 0)
    n.st n.record (k : Time)
  have hout : out.1 = (NamedRun.stateBefore S run (i + 1) 0).st := by
    rw [Proofs.NamedRuntime.stateBefore_tick S run he]
    rfl
  have emit_out : ∀ {o : Object (Fin 2)}, o ∈ out.2.2 →
      o ∈ NamedRun.emittedAt S run i 0 (k : Time) := by
    intro o ho
    change o ∈ (Execution.NamedNode.tick S 0
      (NamedRun.stateBefore S run i 0) (k : Time)).2
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
        simpa only [Execution.NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact Or.inr ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [Execution.NamedNode.tick, n, c, gc, out] using hem)⟩
  · intro B hB u hu
    have hB' : B ∈ out.1.bodies := by
      rw [hout]
      exact hB
    by_cases hpre : B ∈ n.st.bodies
    · exact emitBefore_mono (Nat.le_succ _)
        (hstate.body_gf B hpre u hu)
    · have hnew := Proofs.Bridges.on_tick_emit_T_mem S 0 n (k : Time) (by
        simpa only [Execution.NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_gf_origin (i := i) (t := (k : Time))
            (by simpa only [Execution.NamedNode.tick, n, c, gc, out] using hem)
            hstate hu)
  · intro B hB a ha
    have hB' : B ∈ out.1.bodies := by
      rw [hout]
      exact hB
    by_cases hpre : B ∈ n.st.bodies
    · exact emitBefore_mono (Nat.le_succ _)
        (hstate.body_row B hpre a ha)
    · have hnew := Proofs.Bridges.on_tick_emit_T_mem S 0 n (k : Time) (by
        simpa only [Execution.NamedNode.tick, n, c, gc, out] using hB')
      rcases hnew with hold | hem
      · exact False.elim (hpre hold)
      · exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_row_origin (i := i) (t := (k : Time))
            (by simpa only [Execution.NamedNode.tick, n, c, gc, out] using hem)
            hstate ha)
  · intro k' u hu
    have hstamps : Protocol.PoolStamps
        (NamedRun.stateBefore S run (i + 1) 0).st.core :=
      Protocol.poolStamps_stateBefore S scheduleWellFormed 0 (i + 1)
    have hslot : u.slot = k' := hstamps.slot k' u hu
    have huAfter : u ∈
        (NamedRun.stateBefore S run (i + 1) 0).st.core.gf_votes u.slot := by
      rw [hslot]
      exact hu
    by_cases hheld : u ∈ n.st.core.pool u.slot
    · exact emitBefore_mono (Nat.le_succ _) (hstate.gf u.slot u
        (by simpa [n, Protocol.Store.pool] using hheld))
    · have huout : u ∈ out.1.core.pool u.slot := by
        rw [hout]
        simpa only [Protocol.Store.pool, List.mem_toFinset] using huAfter
      have hnew := Proofs.NamedReceiptCallsGF.tick_new_vote_origin gc S.E S.hc
        S.cfg (S.node 0) n.st n.record (k : Time) u hheld (by
          simpa only [out] using huout)
      rcases hnew with hdirect | ⟨B, hblock, hnot, hpost⟩
      · exact ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [out] using hdirect)⟩
      · have hblock' : Object.block B ∈
            NamedRun.emittedAt S run i 0 (k : Time) :=
          emit_out (by simpa only [out] using hblock)
        exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_gf_origin (i := i) (t := (k : Time)) hblock' hstate
          (by
            have hcall := Proofs.NamedReceiptCallsBase.blockCallAt_self S run he
              (by simpa only [out] using hblock)
            have horigin := Proofs.NamedReceiptCallsGF.block_with_new_vote_origin
              S run i 0 B
              (NamedActionReads.confirmationReadFrom S n (k : Time)).st
              hcall u (by
                simpa [NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock, n] using hheld) hpost
            obtain ⟨j, hj⟩ := horigin
            exact List.mem_of_getElem? hj.2.2.2))
  · intro k' a ha
    have hround := Proofs.NamedStoreBridge.sgRowRounds_stateBefore S run
      (i + 1) 0 k' a ha
    have haout : a ∈ out.1.sg_rows a.round := by
      rw [hout]
      simpa [hround] using ha
    by_cases hheld : a ∈ n.st.sg_rows a.round
    · exact emitBefore_mono (Nat.le_succ _) (hstate.row a.round a hheld)
    · have hnew := Proofs.NamedReceiptCallsF1.tick_new_full_row_origin gc S.E S.hc
        S.cfg (S.node 0) n.st n.record (k : Time) a hheld (by
          simpa only [out] using haout)
      rcases hnew with hdirect | ⟨B, hblock, hnot, hpost⟩
      · exact ⟨i, Nat.lt_succ_self i, (k : Time), he,
          emit_out (by simpa only [out] using hdirect)⟩
      · have hblock' : Object.block B ∈
            NamedRun.emittedAt S run i 0 (k : Time) :=
          emit_out (by simpa only [out] using hblock)
        exact emitBefore_mono (Nat.le_succ _)
          (emitted_block_row_origin (i := i) (t := (k : Time)) hblock' hstate
          (by
            have hcall := Proofs.NamedReceiptCallsBase.blockCallAt_self S run he
              (by simpa only [out] using hblock)
            have horigin := Proofs.NamedReceiptCallsF1.block_full_marker_origin
              S run i 0 B
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
          simpa [NamedRun.stateBefore, NamedWorld.init,
            Execution.NamedNode.initial, Protocol.NamedStore.initial] using hB
        subst B
        simp [NamedBlock.gf_votes] at hu
      · intro B hB a ha
        have hgen : B = NamedBlock.genesis := by
          simpa [NamedRun.stateBefore, NamedWorld.init,
            Execution.NamedNode.initial, Protocol.NamedStore.initial] using hB
        subst B
        simp [NamedBlock.attestations] at ha
      · intro k u hu
        have : False := by
          simpa [NamedRun.stateBefore, NamedWorld.init,
            Execution.NamedNode.initial, Protocol.NamedStore.initial,
            Protocol.Store.init] using hu
        exact this.elim
      · intro k a ha
        exact (by simpa [NamedRun.stateBefore, NamedWorld.init,
          Execution.NamedNode.initial, Protocol.NamedStore.initial] using ha : False).elim
  | succ i ih =>
      cases he : run.events[i]? with
      | none =>
          have hsame : NamedRun.stateBefore S run (i + 1) 0 =
              NamedRun.stateBefore S run i 0 := by
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

theorem tickEvents_objects_empty (start count : Nat) :
    (tickEvents start count).filterMap NamedEvent.object? = [] := by
  induction count generalizing start with
  | zero => simp [tickEvents]
  | succ count ih =>
      simp only [tickEvents, List.filterMap_cons, NamedEvent.object?]
      exact ih (start + 1)

theorem run_objects_empty : NamedRun.objects run = [] := by
  change (tickEvents 0 (trace.eventCount + 1)).filterMap NamedEvent.object? = []
  exact tickEvents_objects_empty 0 (trace.eventCount + 1)

theorem ancestor_body_mem {st : Protocol.NamedStore (Fin 2)}
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

theorem block_origin_of_scope {B : NamedBlock (Fin 2)}
    (hB : NamedRun.blockInRun S run B) :
    B = NamedBlock.genesis ∨ ∃ t : Time, NamedRun.emits S run 0 (.block B) t := by
  obtain ⟨C, hC, hBC⟩ := hB
  rcases hC with hobj | ⟨v, hv, i, hCbody⟩
  · rw [run_objects_empty] at hobj
    simp at hobj
  · have hv0 : v = 0 := by
      exact honest_mem_eq_zero hv
    subst v
    have hAbody : B ∈ (NamedRun.stateBefore S run i 0).st.bodies :=
      ancestor_body_mem
        ((Proofs.NamedRuntime.stateBefore_invariants S run i 0).1.1.1.2.2.1)
        hCbody hBC
    rcases (originState i).body B hAbody with hgen | horigin
    · exact Or.inl hgen
    · exact Or.inr (emitBefore_emits horigin)

theorem emitBefore_le_eventTime {i : Nat} {t : Time} {o : Object (Fin 2)}
    (he : run.events[i]? = some (.tick 0 t)) (h : EmitBefore i o) :
    ∃ t' : Time, t' ≤ t ∧ NamedRun.emits S run 0 o t' := by
  rcases h with ⟨j, hji, t', hj, ho⟩
  have hnonneg_all : ∀ e ∈ run.events, 0 ≤ e.time := by
    intro e he'
    exact (scheduleWellFormed.in_horizon e he').1
  have hclock : t' ≤
      (NamedRun.stateBefore S run i 0).st.core.t :=
    Proofs.NamedRuntime.tick_time_le_clock S run scheduleWellFormed.sorted
      hnonneg_all hj hji
  have hcurrent :
      (NamedRun.stateBefore S run i 0).st.core.t ≤ t :=
    Proofs.NamedRuntime.stateBefore_clock_le_event S run scheduleWellFormed.sorted
      he ((scheduleWellFormed.in_horizon _ (List.mem_of_getElem? he)).1) 0
  exact ⟨t', hclock.trans hcurrent, ⟨j, hj, ho⟩⟩

theorem emitted_block_gf_before {B : NamedBlock (Fin 2)} {t : Time}
    (hB : NamedRun.emits S run 0 (.block B) t)
    {u : GoldfishVote (Fin 2)} (hu : u ∈ B.gf_votes) :
    ∃ t' : Time, t' ≤ t ∧ NamedRun.emits S run 0 (.gfVote u) t' := by
  obtain ⟨i, hi, hmem⟩ := hB
  exact emitBefore_le_eventTime hi
    (emitted_block_gf_origin (i := i) (t := t) hmem (originState i) hu)

theorem emitted_block_row_before {B : NamedBlock (Fin 2)} {t : Time}
    (hB : NamedRun.emits S run 0 (.block B) t)
    {a : NamedAttestation (Fin 2)} (ha : a ∈ B.attestations) :
    ∃ t' : Time, t' ≤ t ∧ NamedRun.emits S run 0 (.attest a) t' := by
  obtain ⟨i, hi, hmem⟩ := hB
  exact emitBefore_le_eventTime hi
    (emitted_block_row_origin (i := i) (t := t) hmem (originState i) ha)

theorem emits_only_zero {v : Fin 2} {o : Object (Fin 2)} {t : Time}
    (h : NamedRun.emits S run v o t) : v = 0 := by
  obtain ⟨i, hi, -⟩ := h
  obtain ⟨k, hk⟩ := event_at_tick hi
  simpa using congrArg NamedEvent.node hk

theorem row_origin_of_scope {a : NamedAttestation (Fin 2)}
    (ha : NamedRun.attestationInRun S run a) :
    ∃ t : Time, NamedRun.emits S run 0 (.attest a) t := by
  rcases ha with hprocess | hcarried | hpool
  · obtain ⟨v, t, hp⟩ := hprocess
    rcases hp with hem | hdel
    · have hv : v = 0 := emits_only_zero hem
      subst v
      exact ⟨t, hem⟩
    · obtain ⟨j, hj⟩ := hdel
      exact False.elim (no_delivery_at_index hj)
  · obtain ⟨B, hB, haB⟩ := hcarried
    rcases block_origin_of_scope hB with hgen | ⟨t, hEmit⟩
    · subst B
      simp [NamedBlock.attestations] at haB
    · obtain ⟨t', -, hem⟩ := emitted_block_row_before hEmit haB
      exact ⟨t', hem⟩
  · obtain ⟨v, hv, i, haPool⟩ := hpool
    have hv0 : v = 0 := honest_mem_eq_zero hv
    subst v
    exact emitBefore_emits ((originState i).row a.round a haPool)

theorem emitted_author_zero {v : Fin 2} {o : Object (Fin 2)} {t : Time}
    (h : NamedRun.emits S run v o t) : NamedObject.author o = some 0 := by
  have hv : v = 0 := emits_only_zero h
  subst v
  cases o with
  | block B =>
      obtain ⟨i, hi, hmem⟩ := h
      exact emitted_block_fields hmem |>.2.2
  | gfVote u =>
      have hs := Proofs.Optimistic.emits_gfVote_shape S h
      have hu : u.val_index = 0 := hs.2.2.1
      simpa [NamedObject.author, hu]
  | attest a =>
      have hs := Proofs.Optimistic.emits_attest_shape S h
      have ha : a.val_index = 0 := hs.1
      simpa [NamedObject.author, ha]

theorem authentic : Unforgeable S run where
  unforgeable := by
    intro v o t hprocess u hu hauthor
    rcases hprocess with hem | hdel
    · have hv : v = 0 := emits_only_zero hem
      have hauth := emitted_author_zero hem
      have hu0 : u = 0 := Option.some.inj (hauthor.symm.trans hauth)
      subst v
      subst u
      exact ⟨t, le_rfl, hem⟩
    · obtain ⟨j, hj⟩ := hdel
      exact False.elim (no_delivery_at_index hj)

  carried_gf := by
    intro v B t hprocess u hu hHon
    rcases hprocess with hem | hdel
    · have hv : v = 0 := emits_only_zero hem
      subst v
      have hu0 : u.val_index = 0 := honest_mem_eq_zero hHon
      simpa [hu0] using emitted_block_gf_before hem hu
    · obtain ⟨j, hj⟩ := hdel
      exact False.elim (no_delivery_at_index hj)

  carried_attest := by
    intro v B t hprocess a ha hHon
    rcases hprocess with hem | hdel
    · have hv : v = 0 := emits_only_zero hem
      subst v
      have ha0 : a.val_index = 0 := honest_mem_eq_zero hHon
      simpa [ha0] using emitted_block_row_before hem ha
    · obtain ⟨j, hj⟩ := hdel
      exact False.elim (no_delivery_at_index hj)

theorem emitted_block_root {B : NamedBlock (Fin 2)} {t : Time}
    (hB : NamedRun.emits S run 0 (.block B) t) :
    B.root = ⟨B.slot + 1⟩ := by
  obtain ⟨i, hi, hmem⟩ := hB
  have hfields := emitted_block_fields hmem
  calc
    B.root = (S.node 0).new_root
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.s := hfields.2.1
    _ = ⟨(NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S run i 0) t).st.core.s + 1⟩ := by
      rfl
    _ = ⟨B.slot + 1⟩ := by rw [← hfields.1]

theorem rootCollisionFree : RootCollisionFree S run where
  root_injective := by
    intro B C hB hC A D hA hD hroot
    have hAscope : NamedRun.blockInRun S run A := by
      rcases hA with hAB | hAC
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S run hB hAB
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S run hC hAC
    have hDscope : NamedRun.blockInRun S run D := by
      rcases hD with hDB | hDC
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S run hB hDB
      · exact Proofs.NamedRuntime.blockInRun_of_ancestor S run hC hDC
    rcases block_origin_of_scope hAscope with hAgen | ⟨tA, hAemit⟩
    · rcases block_origin_of_scope hDscope with hDgen | ⟨tD, hDemit⟩
      · simpa [hAgen, hDgen]
      · subst A
        have hzero : (0 : Nat) = D.slot + 1 := by
          rw [emitted_block_root hDemit] at hroot
          exact congrArg BlockId.value hroot
        change 0 = Nat.succ D.slot at hzero
        cases hzero
    · rcases block_origin_of_scope hDscope with hDgen | ⟨tD, hDemit⟩
      · subst D
        have hzero : A.slot + 1 = (0 : Nat) := by
          rw [emitted_block_root hAemit] at hroot
          exact congrArg BlockId.value hroot
        change Nat.succ A.slot = 0 at hzero
        cases hzero
      · have hslot : A.slot = D.slot := by
          have hvalue := congrArg BlockId.value hroot
          rw [emitted_block_root hAemit, emitted_block_root hDemit] at hvalue
          change Nat.succ A.slot = Nat.succ D.slot at hvalue
          exact Nat.succ.inj hvalue
        exact Proofs.HealingSurface.emits_block_unique S scheduleWellFormed
          hAemit hDemit hslot

theorem admissibleCore : AdmissibleCore S run := {
  toNamedScheduleWellFormed := scheduleWellFormed
  toNamedDeliveryWellFormed := deliveryWellFormed
  toNamedRootCollisionFree := rootCollisionFree
  toNamedUnforgeable := authentic }

theorem admissible : Admissible S run := {
  toExecutionValid := admissibleCore
  toNamedSynchrony := synchrony
  all_awake := by
    intro v hv r hpost hhor
    exact awake_all v hv r hhor }

theorem awake_window_honest_mem (r : Round) (hr : 0 < r) :
    (0 : Fin 2) ∈ honestAwakeWindow (fun v => (S.node v).awake)
      run.honest S.hc.η_SG r := by
  apply Finset.mem_filter.mpr
  refine ⟨honest_zero, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨r - 1, ?_, ?_⟩
  · exact Protocol.pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr
  · rfl

theorem awake_window_eq_honest (r : Round) (hr : 0 < r) :
    honestAwakeWindow (fun v => (S.node v).awake)
      run.honest S.hc.η_SG r = ({0} : Finset (Fin 2)) := by
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

theorem awake_window_majority : ∀ r, 0 < r → S.a (r - 1) ≤ run.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) run.honest S.hc.η_SG r := by
  intro r hr hhor
  rw [AwakeWindowMajority, awake_window_eq_honest r hr]
  have hcomp : (Finset.univ \ run.honest) = ({1} : Finset (Fin 2)) := by
    change (Finset.univ \ ({0} : Finset (Fin 2))) = ({1} : Finset (Fin 2))
    ext v
    fin_cases v <;> simp
  rw [hcomp]
  change (1 : Nat) < 3
  norm_num

theorem slashableBound : SlashableBound S run :=
  Proofs.HealingSurface.slashableBound_of_admissibleCore_belowOneThird
    S (Proofs.AdmissibleCore.ofParts admissibleCore synchrony) belowOneThird

end Trace

theorem strongRecoveryPrefix : Statements.StrongRecoveryPrefix S sourceRun
    rGST gap extra prefixEnd := by
  letI : TickTrace := sourceTrace
  refine {
    execution := admissibleCore
    synchrony := synchrony
    allAwake := by
      intro v hv r hpost hhor
      exact awake_all v hv r hhor
    committees := honestCommittees
    belowThird := belowOneThird
    recurrence := proposerRecurrence
    timeout := timeoutDelayBound
    postGST := postGST
    start := boundedPhaseStart
    horizon := ?_ }
  change (eventCount : Time) = S.a (prefixEnd + gap)
  exact horizonTime_coe

theorem generic_recovery_regime :
    Statements.Generic.RecoveryRegime
      (DecoupledConsensusModel.Execution.spec S)
      (Statements.Instantiation.env S)
      (Statements.Instantiation.interface S)
      (Statements.Instantiation.constants S)
      sourceRun (S.a rGST) gap := by
  letI : TickTrace := sourceTrace
  have hround : Statements.Instantiation.roundAt S (S.a rGST) = rGST := by
    apply Nat.le_antisymm
    · by_contra hnot
      exact (Statements.roundAt_min S (S.a rGST)
        (Nat.lt_of_not_ge hnot)) le_rfl
    · by_contra hnot
      have hlt : Statements.Instantiation.roundAt S (S.a rGST) < rGST :=
        Nat.lt_of_not_ge hnot
      have hstrict : S.a (Statements.Instantiation.roundAt S (S.a rGST)) < S.a rGST := by
        unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
        push_cast
        have hR : (0 : Time) < (S.hc.R : Time) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
        have hrt : (Statements.Instantiation.roundAt S (S.a rGST) : Time) < (rGST : Time) := by
          exact_mod_cast hlt
        have hmul := mul_lt_mul_of_pos_right hrt hR
        have hmul' := mul_lt_mul_of_pos_left hmul
          (show (0 : Time) < 4 * S.E.Δ by nlinarith [S.E.Δ_pos])
        change 4 * S.E.Δ *
            ((Statements.Instantiation.roundAt S (S.a rGST) : Time) * (S.hc.R : Time)) +
              6 * S.E.Δ <
          4 * S.E.Δ * ((rGST : Time) * (S.hc.R : Time)) + 6 * S.E.Δ
        nlinarith [hmul']
      exact (not_lt_of_ge (Statements.roundAt_spec S (S.a rGST))) hstrict
  refine {
    execution := Proofs.genericExecutionValid_of_named S sourceRun admissibleCore
    partialSynchrony := Proofs.genericPartialSynchrony_of_named S sourceRun synchrony
    gst := by simpa [Statements.Instantiation.env] using postGST
    committees := ?_
    belowThird := ?_
    allAwake := ?_
    recurrence := generic_proposer_recurrence
    horizon := ?_ }
  · intro s
    simpa [Statements.Instantiation.interface, Statements.instance] using honestCommittees s
  · simpa [Statements.Instantiation.env, Statements.Generic.BelowOneThird,
      Execution.BelowOneThird] using belowOneThird
  · intro v hv t ht hhor
    rfl
  · change sourceRun.horizon =
      S.a (Statements.Instantiation.recoveryRound S (S.a rGST) gap S.extraRounds)
    have hextra : S.extraRounds = extra := by
      norm_num [Setup.extraRounds, S, hc, cfg, extra]
    rw [hextra]
    have hrecovery : Statements.Instantiation.recoveryRound S (S.a rGST) gap extra = prefixEnd + gap := by
      unfold Statements.Instantiation.recoveryRound prefixEnd
      rw [hround]
      norm_num [Statements.Instantiation.boundedPhaseStartLag, phaseLag, gap, extra]
    rw [hrecovery]
    exact horizonTime_coe

theorem weakContinuation : Statements.WeakContinuation S sourceRun continuationRun
    (prefixEnd + gap) := by
  letI : TickTrace := continuationTrace
  refine {
    execution := admissibleCore
    synchrony := synchrony
    committees := honestCommittees
    accountable := slashableBound
    agrees := source_continuation_agrees
    covered := ?_
    windows := ?_ }
  · change healingBoundaryTime S (prefixEnd + gap) ≤
      (continuationEventCount : Time)
    exact le_rfl
  · intro r hr hhor
    apply awake_window_majority r
    · exact lt_of_le_of_lt (Nat.zero_le _) hr
    · exact hhor

theorem boundedSafety_activated :
    ∃ m, prefixEnd ≤ m ∧ m ≤ prefixEnd + gap ∧ prefixEnd + gap ≤ m + gap ∧
      ∃ P : NamedBlock (Fin 2),
        Statements.Instantiation.proposedBlockAt S sourceRun (S.hc.opening_slot m) = some P ∧
        Internal.PhaseShiftSafety S continuationRun prefixEnd
          (S.hc.opening_slot m) P.erase := by
  obtain ⟨m, hm₁, hm₂, hm₃, P, hP, hcontinuations⟩ :=
    Proofs.boundedSafety S sourceRun rGST gap extra prefixEnd strongRecoveryPrefix
  exact ⟨m, hm₁, hm₂, hm₃, P, hP,
    hcontinuations continuationRun weakContinuation⟩

theorem vote_safety_after_recovery_activated :
    ∃ cutScale, 0 < cutScale ∧
      Statements.WeakVoteContinuation S sourceRun rGST gap cutScale := by
  letI : TickTrace := sourceTrace
  obtain ⟨cutScale, hpos, hsafe⟩ :=
    Proofs.voteSafety S extra timeoutDelayBound gap
  exact ⟨cutScale, hpos,
    hsafe sourceRun rGST admissible honestCommittees belowOneThird postGST
      proposerOpeningCarrierRecurrence⟩

theorem stableSafety_activated :
    ∃ m, prefixEnd ≤ m ∧ m ≤ prefixEnd + gap ∧
      StableRecordCanonicalFrom S continuationRun (healingBoundaryTime S m) := by
  obtain ⟨m, hm₁, hm₂, hcanonical⟩ :=
    (Proofs.stableSafety S).afterGST sourceRun rGST gap extra prefixEnd
      strongRecoveryPrefix
  exact ⟨m, hm₁, hm₂, hcanonical continuationRun weakContinuation⟩

theorem honestProposalConfirmation_activated :
    ∃ m, prefixEnd ≤ m ∧ m ≤ prefixEnd + gap ∧ prefixEnd + gap ≤ m + gap ∧
      Statements.HonestProposalsConfirmedFrom S continuationRun
        (S.hc.opening_slot m) := by
  obtain ⟨m, hm₁, hm₂, hm₃, hconfirmed⟩ :=
    (Proofs.honestProposalConfirmation S).afterGST sourceRun rGST gap extra prefixEnd
      strongRecoveryPrefix
  exact ⟨m, hm₁, hm₂, hm₃, hconfirmed continuationRun weakContinuation⟩

theorem availableChainGrowth_activated :
    ∃ m, prefixEnd ≤ m ∧ m ≤ prefixEnd + gap ∧ prefixEnd + gap ≤ m + gap ∧
      AvailableChainGrowthFrom S continuationRun (S.hc.opening_slot m) gap := by
  letI : TickTrace := continuationTrace
  obtain ⟨m, hm₁, hm₂, hm₃, hgrowth⟩ :=
    (Proofs.availableChainGrowth S).afterGST sourceRun rGST gap extra prefixEnd
      strongRecoveryPrefix
  exact ⟨m, hm₁, hm₂, hm₃,
    hgrowth continuationRun weakContinuation gap proposerOpeningCarrierRecurrence⟩

theorem stableRecordGrowth_activated :
    ∃ m, prefixEnd ≤ m ∧ m ≤ prefixEnd + gap ∧
      StableRecordGrowthFrom S continuationRun (S.hc.opening_slot m)
        (gap + S.hc.η_SG - 1) := by
  letI : TickTrace := continuationTrace
  obtain ⟨m, hm₁, hm₂, hgrowth⟩ :=
    (Proofs.stableRecordGrowth S).afterGST sourceRun rGST gap extra prefixEnd
      strongRecoveryPrefix
  exact ⟨m, hm₁, hm₂,
    hgrowth continuationRun weakContinuation gap proposerOpeningCarrierRecurrence⟩


structure StrongRecoveryPrimitiveFacts : Prop where
  schedule : ScheduleWellFormed S sourceRun
  delivery : DeliveryWellFormed S sourceRun
  roots : RootCollisionFree S sourceRun
  authentic : Unforgeable S sourceRun
  committees : HonestCommittees S sourceRun.honest
  belowThird : BelowOneThird S sourceRun.honest
  recurrence : MultiProposerRecurrence S sourceRun gap
  timeout : TimeoutDelayBound S extra
  postGST : S.E.t_GST ≤ S.a rGST
  start : Internal.BoundedPhaseStart S sourceRun rGST gap extra prefixEnd
  horizon : sourceRun.horizon = S.a (prefixEnd + gap)
  awake : ∀ v ∈ sourceRun.honest, ∀ r : Round, S.a r ≤ sourceRun.horizon →
    (S.node v).awake r = true
  synchrony : Synchrony S sourceRun

theorem exactHorizon : sourceRun.horizon = S.a (prefixEnd + gap) := by
  change (eventCount : Time) = S.a (prefixEnd + gap)
  exact horizonTime_coe

theorem strongRecoveryPrimitiveFacts : StrongRecoveryPrimitiveFacts := by
  letI : TickTrace := sourceTrace
  exact {
    schedule := scheduleWellFormed
    delivery := deliveryWellFormed
    roots := rootCollisionFree
    authentic := authentic
    committees := honestCommittees
    belowThird := belowOneThird
    recurrence := proposerRecurrence
    timeout := timeoutDelayBound
    postGST := postGST
    start := boundedPhaseStart
    horizon := exactHorizon
    awake := awake_all
    synchrony := synchrony }

#print axioms tickEvents_objects_empty
#print axioms emitBefore_mono
#print axioms emitBefore_emits
#print axioms orderedBodies_mem
#print axioms emitted_block_fields
#print axioms emitted_block_gf_origin
#print axioms emitted_block_row_origin
#print axioms originState_tick
#print axioms originState
#print axioms run_objects_empty
#print axioms ancestor_body_mem
#print axioms block_origin_of_scope
#print axioms emitBefore_le_eventTime
#print axioms emitted_block_gf_before
#print axioms emitted_block_row_before
#print axioms emits_only_zero
#print axioms row_origin_of_scope
#print axioms emitted_author_zero
#print axioms authentic
#print axioms emitted_block_root
#print axioms rootCollisionFree
#print axioms admissibleCore
#print axioms admissible
#print axioms awake_window_honest_mem
#print axioms awake_window_eq_honest
#print axioms awake_window_majority
#print axioms slashableBound
#print axioms strongRecoveryPrefix
#print axioms weakContinuation
#print axioms boundedSafety_activated
#print axioms vote_safety_after_recovery_activated
#print axioms stableSafety_activated
#print axioms honestProposalConfirmation_activated
#print axioms availableChainGrowth_activated
#print axioms stableRecordGrowth_activated
#print axioms exactHorizon
#print axioms strongRecoveryPrimitiveFacts

end Witnesses.StrongRecovery
end DecoupledConsensusModel

end
