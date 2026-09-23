module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransport
public import DecoupledConsensusProofs.Protocol.Grades.GradeCutoffMono
public import DecoupledConsensusProofs.Protocol.Grades.GuardedGradeHelpers
public import DecoupledConsensusProofs.Protocol.Handlers.RawRelay
public import DecoupledConsensusProofs.Protocol.Store.RawSource
public import DecoupledConsensusProofs.Protocol.Handlers.HealthyLateRelay
public import DecoupledConsensusProofs.Execution.FinalityAgreement
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.Ladder
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.HeldSkipProducers

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Private arbitrary-sender relay kernel

The G1-to-G0 cutoff adapters use the same named-row handler proof as the
available G2-to-G1 adapters. It stays private to this module.
-/

section PrivateRelayKernel

open Internal.NamedOutageEntry Internal.NamedStableChainOutage

private def Carry (before after : Protocol.NamedStore V) : Prop :=
  ∀ a : NamedAttestation V, a ∈ before.sg_rows a.round →
    a ∈ after.sg_rows a.round ∧
      after.core.timestamp_sg_vote (Protocol.sgVote a.erase) =
        before.core.timestamp_sg_vote (Protocol.sgVote a.erase)

omit [Fintype V] in
private theorem finality_stamp (st : Protocol.Store V) (sigma : Protocol.ChainState V) :
    (Protocol.update_finality st sigma).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

private theorem gf_checked_stamp (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> rfl

private theorem gf_fold_stamp (E : Env V) (st : Protocol.Store V) (rows : List (GoldfishVote V)) :
    (rows.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_sg_vote =
      st.timestamp_sg_vote := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, gf_checked_stamp]

private theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

private theorem core_block_stamp (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_sg_vote =
      st.core.timestamp_sg_vote := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · rw [NamedStore.commit_core]
    unfold Protocol.on_block_checked_using
    split_ifs
    · dsimp only [Protocol.on_block_using]
      split_ifs <;> first
        | rfl
        | (rw [finality_stamp, gf_fold_stamp])
    · rfl
  · rfl

private theorem row_carry (S : Setup V) (st : Protocol.NamedStore V) (incoming : NamedAttestation V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedAdmission.admit_row S.hc st incoming) := by
  intro a ha
  exact ⟨NamedReceiptCallsF1.admit_row_mem_mono S.hc st incoming a ha,
    NamedAdmission.existing_row_stamp S.hc st hcoh.2.2.2.1 incoming a ha⟩

private theorem propose_coherent (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Proofs.NamedStore.Coherent S.E S.cfg
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact hcoh
  · exact NamedAdmission.coherent_on_block .alsoCarried S.E S.hc S.cfg st _ hcoh

/-- Every held row is in its own bucket and has a real first projected
stamp at or before this fixed bound. No body condition is included. -/
private def Data (bound : Time) (st : Protocol.NamedStore V) : Prop :=
  st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
      st.core.timestamp_sg_vote (Protocol.sgVote a.erase) = some (stamp : Stamp)

omit [DecidableEq V] [Fintype V] in
private theorem data_fields {bound : Time} {st out : Protocol.NamedStore V}
    (h : Data bound st) (hr : out.sg_rows = st.sg_rows)
    (hs : out.core.timestamp_sg_vote = st.core.timestamp_sg_vote)
    (ht : out.core.t = st.core.t) : Data bound out := by
  exact ⟨by simpa only [ht] using h.1, by simpa only [hr, hs] using h.2⟩

omit [Fintype V] in
private theorem row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

private theorem row_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (incoming : NamedAttestation V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hd : Data bound st) : Data bound (Protocol.NamedAdmission.admit_row S.hc st incoming) := by
  refine ⟨?_, ?_⟩
  · simpa only [(NamedAdmission.admit_row_fixed_fields S.hc st incoming).1] using hd.1
  · intro k a ha
    rcases row_mem_cases_at S.hc st incoming a k ha with hold | hnew
    · obtain ⟨hr, stamp, hstampBound, hstamp⟩ := hd.2 k a hold
      have hown : a ∈ st.sg_rows a.round := by simpa only [hr] using hold
      refine ⟨hr, stamp, hstampBound, ?_⟩
      exact ((row_carry S st incoming hcoh) a hown).2.trans hstamp
    · obtain ⟨haeq, hkeq⟩ := hnew
      subst a
      subst k
      by_cases hold : incoming ∈ st.sg_rows incoming.round
      · obtain ⟨_, stamp, hstampBound, hstamp⟩ := hd.2 incoming.round incoming hold
        exact ⟨rfl, stamp, hstampBound,
          ((row_carry S st incoming hcoh) incoming hold).2.trans hstamp⟩
      · exact ⟨rfl, st.core.t, hd.1,
          NamedReceiptCallsF1.full_new_row_stamp S.hc st incoming hold ha⟩

private theorem rows_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hd : Data bound st) : Data bound (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows generalizing st with
  | nil => exact hd
  | cons a rows ih =>
    exact ih _ (NamedAdmission.coherent_admit_row S.E S.hc S.cfg st a hcoh)
      (row_data S bound st a hcoh hd)

private theorem core_block_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hd : Data bound st) :
    Data bound (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) :=
  data_fields hd (core_block_rows S st B) (core_block_stamp S st B)
    (NamedAdmission.process_block_clock S.E S.hc S.cfg st B).1

private theorem block_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hc := NamedStore.coherent_process_block S.E S.hc S.cfg st B hcoh
  have hdcore := core_block_data S bound st B hd
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_data S bound _ B.attestations hc hdcore
  · exact hdcore

private theorem propose_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact hd
  · exact block_data S bound st _ hcoh hd

private theorem gf_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact data_fields hd rfl (gf_checked_stamp S.E _ _)
      (on_goldfish_vote_checked_time S.E _ _)
  · exact hd

private theorem confirmation_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (st : Protocol.NamedStore V) (s : Slot) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) :=
  data_fields hd rfl rfl rfl

private theorem clock_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (t : Time) (ht : t ≤ bound) (hd : Data bound st) :
    Data bound (Protocol.NamedStore.setClock S.E st t) := ⟨ht, hd.2⟩

/-- Fixed-time scheduler induction used only with the concrete facts below. -/
private theorem tick_preserves (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (t : Time) (P : Protocol.NamedStore V → Prop)
    (hclock : ∀ st, P st → P (Protocol.NamedStore.setClock S.E st t))
    (hprop : ∀ st, P st → P (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1)
    (hgf : ∀ st, P st → P (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1)
    (hconf : ∀ st s, P st → P (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s))
    (hatt : ∀ st record, P st → P (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (h : P st) :
    P (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> solve_by_elim (maxDepth := 10) [hclock, hprop, hgf, hconf, hatt]

private theorem tick_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (ht : t ≤ bound) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  let P := fun st : Protocol.NamedStore V => Proofs.NamedStore.Coherent S.E S.cfg st ∧ Data bound st
  have hclock : ∀ st, P st → P (Protocol.NamedStore.setClock S.E st t) := by
    intro st hs
    exact ⟨NamedStore.coherent_clock S.E S.cfg st t hs.1, clock_data S bound st t ht hs.2⟩
  have hprop : ∀ st, P st →
      P (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
    intro st hs
    exact ⟨propose_coherent gc S nd st hs.1, propose_data gc S bound nd st hs.1 hs.2⟩
  have hgf : ∀ st, P st → P (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
    intro st hs
    exact ⟨NamedDuties.coherent_goldfish_vote gc S.E S.hc S.cfg nd st hs.1,
      gf_data gc S bound nd st hs.2⟩
  have hconf : ∀ st s, P st →
      P (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) := by
    intro st s hs
    exact ⟨NamedDuties.coherent_confirmation gc S.E S.hc S.cfg st s hs.1,
      confirmation_data gc S bound st s hs.2⟩
  have hatt : ∀ st record, P st →
      P (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 := by
    intro st record hs
    exact ⟨NamedAdmission.coherent_admit_row S.E S.hc S.cfg st _ hs.1,
      row_data S bound st _ hs.1 hs.2⟩
  exact (tick_preserves gc S nd t P hclock hprop hgf hconf hatt st record ⟨hcoh, hd⟩).2

private theorem process_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (o : NamedObject V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_data S bound st B hcoh hd
  | gfVote u =>
    exact data_fields hd rfl (gf_checked_stamp S.E st.core u)
      (on_goldfish_vote_checked_time S.E st.core u)
  | attest a => exact row_data S bound st a hcoh hd

private theorem prefix_data (S : Setup V) (rho : NamedRun V) (bound : Time) (hzero : 0 ≤ bound)
    (i : Nat) (hbefore : ∀ j e, j < i → rho.events[j]? = some e → e.time ≤ bound)
    (reader : V) : Data bound (NamedRun.stateBefore S rho i reader).st := by
  revert hbefore
  induction i with
  | zero =>
    intro _
    refine ⟨hzero, ?_⟩
    intro k a ha
    simp only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, List.not_mem_nil] at ha
  | succ i ih =>
    intro hbefore
    have hd := ih (fun j e hj he => hbefore j e (Nat.lt_succ_of_lt hj) he)
    have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => exact hd
    | some e =>
      change Data bound (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
      have ht := hbefore i e (Nat.lt_succ_self i) he
      by_cases hv : reader = e.node
      · cases e with
        | tick v t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_tick]
          exact tick_data _ S bound (S.node reader) _ _ t ht hcoh hd
        | deliver v o t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_deliver]
          exact process_data S bound _ o hcoh hd
      · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
        exact hd

omit [DecidableEq V] [Fintype V] in
private theorem event_time_le (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i j : Nat} {e f : NamedEvent V} (he : rho.events[i]? = some e)
    (hf : rho.events[j]? = some f) (hij : i ≤ j) : e.time ≤ f.time := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hf
    have hk := (List.pairwise_iff_getElem.mp hsorted) i j hi hj hij
    rw [hgeti, hgetj] at hk
    rcases Prod.Lex.le_iff.mp hk with hl | ⟨heq, _⟩
    · exact hl.le
    · exact heq.le
  · have hef : e = f := Option.some.inj (he.symm.trans hf)
    exact (congrArg NamedEvent.time hef).le

private theorem data_at_event (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {i : Nat} {e : NamedEvent V}
    (he : rho.events[i]? = some e) (reader : V) :
    Data e.time (NamedRun.stateBefore S rho i reader).st ∧
      Data e.time (NamedRun.stateBefore S rho (i + 1) reader).st := by
  have hn := (sch.in_horizon _ (List.mem_of_getElem? he)).1
  constructor
  · exact prefix_data S rho e.time hn i
      (fun j f hj hf => event_time_le rho sch.sorted hf he hj.le) reader
  · exact prefix_data S rho e.time hn (i + 1)
      (fun j f hj hf => event_time_le rho sch.sorted hf he (Nat.le_of_lt_succ hj)) reader

private theorem stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    (NamedRun.stateBefore S rho i v).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t := by
  induction i with
  | zero =>
    simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => simpa only [Option.toList_none, List.foldl_nil] using ih
    | some e =>
      change (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.s =
        S.E.slotOf (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.t
      by_cases hv : e.node = v
      · cases e with
        | tick u t =>
          change u = v at hv
          subst u
          rw [Proofs.NamedRuntime.step_tick]
          rw [(Proofs.NamedNode.tick_clock S v _ t).1, (Proofs.NamedNode.tick_clock S v _ t).2]
        | deliver u o t =>
          change u = v at hv
          subst u
          rw [Proofs.NamedRuntime.step_deliver]
          rw [(Proofs.NamedNode.process_clock S _ o).1, (Proofs.NamedNode.process_clock S _ o).2]
          exact ih
      · rw [Proofs.NamedRuntime.step_other S _ e v (Ne.symm hv)]
        exact ih


private theorem emitted_block_due (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (B : NamedBlock V)
    (hB : NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2) :
    0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index := by
  by_contra hnot
  rw [NamedTick.tick_computed_duties] at hB
  dsimp only at hB
  simp only [if_neg hnot] at hB
  split_ifs at hB <;>
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, and_false, exists_false] at hB

private theorem handle_event_time (S : Setup V) (rho : NamedRun V)
    {i : Nat} {reader : V} {o : NamedObject V} {td : Time} {e : NamedEvent V}
    (hcall : NamedRun.actualHandlesAt S rho i reader o td)
    (he : rho.events[i]? = some e) : e.time = td := by
  obtain ⟨f, hf, _, ht⟩ := hcall.2
  have hef : e = f := Option.some.inj (he.symm.trans hf)
  exact (congrArg NamedEvent.time hef).trans ht

private theorem tick_le_clock_before_delivery (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {i : Nat} {reader : V} {o : NamedObject V} {td p : Time}
    (he : rho.events[i]? = some (.deliver reader o td))
    (hp : NamedEvent.tick reader p ∈ rho.events) (hpt : p ≤ td) :
    p ≤ (NamedRun.stateBefore S rho i reader).st.core.t := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  have hji : j < i := by
    by_contra hn
    have hij : i ≤ j := Nat.le_of_not_gt hn
    have hne : i ≠ j := by
      intro h
      subst j
      rw [he] at hj
      cases hj
    obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
    have hkey := (List.pairwise_iff_getElem.mp sch.sorted) i j hiLen hjLen (lt_of_le_of_ne hij hne)
    rw [hiGet, hjGet] at hkey
    have hbad : ¬ NamedEvent.key (NamedEvent.deliver reader o td) ≤
        NamedEvent.key (NamedEvent.tick reader p) := by
      simp only [NamedEvent.key, NamedEvent.time, NamedEvent.phase, Prod.Lex.le_iff]
      rintro (hlt | ⟨_, hphase⟩)
      · exact (not_lt_of_ge hpt) hlt
      · norm_num at hphase
    exact hbad hkey
  exact Proofs.NamedRuntime.tick_time_le_clock S rho sch.sorted
    (fun e he => (sch.in_horizon e he).1) hj hji


private theorem tick_rows_after_proposal (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    ∀ a : NamedAttestation V, a ∈ st1.sg_rows a.round →
      a ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.sg_rows a.round := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h32 : st3.sg_rows = st1.sg_rows := by dsimp only [st3, st2]; split_ifs <;> rfl
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true
        then (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  change ∀ row : NamedAttestation V, row ∈ st1.sg_rows row.round →
    row ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.sg_rows row.round
  intro row hrow
  have ha3 : row ∈ st3.sg_rows row.round := by rw [h32]; exact hrow
  rw [hstore]
  split_ifs
  · exact NamedReceiptCallsF1.admit_row_mem_mono S.hc st3 _ row ha3
  · exact ha3

private theorem block_call_rows_after_event (S : Setup V) (rho : NamedRun V)
    {i : Nat} {reader : V} {B : NamedBlock V} {before : Protocol.NamedStore V}
    (hcall : Execution.NamedReceiptCalls.blockCallAt S rho i reader B before)
    (a : NamedAttestation V)
    (ha : a ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B).sg_rows
        a.round) :
    a ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows
      a.round := by
  rcases hcall with ⟨t, he, rfl⟩ | ⟨t, he, hem, rfl⟩
  · rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he]
    exact ha
  · let n := NamedRun.stateBefore S rho i reader
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    have hdue := emitted_block_due (DecoupledConsensusModel.Protocol.frameContract c) S.E S.hc S.cfg
      (S.node reader) n.st n.record t B hem
    have hcallEq := Proofs.NamedReceiptCallsBase.self_proposal_call S rho he hem
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
    apply tick_rows_after_proposal (DecoupledConsensusModel.Protocol.frameContract c) S (S.node reader)
      n.st n.record t a
    simp only [if_pos hdue]
    rw [congrArg Prod.fst hcallEq]
    exact ha

private theorem action_tick_store (S : Setup V) (reader : V) (before : NamedNodeState V)
    (q : Round) (hawake : (S.node reader).awake q = true) :
    (NamedNode.tick S reader before (S.a q)).1.st =
      let n := actionReadFrom S before q
      (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
        S.E S.hc (S.node reader) n.st n.record).1 := by
  have hpos : 0 < S.E.slotOf (S.a q) := by
    rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
    exact Nat.zero_lt_succ _
  have hs : S.a q = Protocol.support_cutoff S.E (S.E.slotOf (S.a q)) := by
    rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
  have hp : ¬ (0 < S.E.slotOf (S.a q) ∧
      S.a q = Protocol.proposal_time S.E (S.E.slotOf (S.a q)) ∧
      S.E.proposer (S.E.slotOf (S.a q)) = (S.node reader).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a q) ∧
      S.a q = Protocol.vote_time S.E (S.E.slotOf (S.a q))) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E _ (hs.symm.trans h.2)
  change (Protocol.NamedTick.tick (NamedProfile.gradeContract (preparedCache S before (S.a q)))
    S.E S.hc S.cfg (S.node reader) before.st before.record (S.a q)).1 = _
  rw [NamedTick.tick_computed_duties]
  simp only [if_neg hp, if_neg hv, if_pos (And.intro hpos hs)]
  have hround : S.hc.round_of (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract (preparedCache S before (S.a q))) S.E S.hc
      (Protocol.NamedStore.setClock S.E before.st (S.a q)) (S.E.slotOf (S.a q) - 1)).core.s = q :=
    Proofs.HealingLemmas.round_of_slotOf_a S q
  simp only [hround, hawake, and_self, if_true]
  rfl


private theorem pool_full_witness (S : Setup V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (k : Round) (b : CombinedAttestation V)
    (hb : b ∈ st.core.sg_pool k) :
    ∃ named : NamedAttestation V, named ∈ st.sg_rows k ∧ named.erase = b := by
  change b ∈ (st.core.sg_votes k).toFinset at hb
  rw [hcoh.2.2.2.1 k] at hb
  exact List.mem_map.mp (List.mem_toFinset.mp hb)


omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- This is a list-prefix equation, not an inference from folded states. -/
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- Every event through j passes the strict filter. Count that actual take
prefix to obtain the post-event index bound, including same-time events. -/
private theorem post_index_le_strict_filter_length (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) :
    j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega



set_option linter.unusedFintypeInType false in
private theorem new_row_round_floor (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows a.round) :
    a.round ≤ hc.round_of st.core.s := by
  have heq : a = incoming :=
    (NamedReceiptCallsF1.admit_row_mem_cases hc st incoming a hpost).resolve_left hpre
  subst incoming
  by_contra hn
  have hfuture : hc.round_of st.core.s < a.round := Nat.lt_of_not_ge hn
  have hcore : Protocol.on_sg_vote hc st.core a.erase = st.core := by
    unfold Protocol.on_sg_vote
    exact if_pos (Or.inr (Or.inl hfuture))
  rw [NamedAdmission.admit_row_of_core_noop hc st a hcore] at hpost
  exact hpre hpost

set_option linter.unusedFintypeInType false in
/-- Extract the first insertion in the whole constant-slot F1 fold. -/
private theorem rows_new_round_floor (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_rows hc st rows).sg_rows a.round) :
    a.round ≤ hc.round_of st.core.s := by
  induction rows generalizing st with
  | nil => exact False.elim (hpre hpost)
  | cons incoming rows ih =>
    change a ∈
      (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st incoming) rows).sg_rows a.round at hpost
    by_cases hmid : a ∈
        (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows a.round
    · exact new_row_round_floor hc st incoming a hpre hmid
    · have hf := ih (Protocol.NamedAdmission.admit_row hc st incoming) hmid hpost
      rw [(NamedAdmission.admit_row_fixed_fields hc st incoming).2.1] at hf
      exact hf

private theorem block_new_round_floor (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round) :
    a.round ≤ S.hc.round_of st.core.s := by
  have hpreCore : a ∉
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows a.round := by
    simpa only [core_block_rows] using hpre
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost
  split_ifs at hpost
  · have hf := rows_new_round_floor S.hc _ B.attestations a hpreCore hpost
    rw [(NamedAdmission.process_block_clock S.E S.hc S.cfg st B).2] at hf
    exact hf
  · exact False.elim (hpreCore hpost)

private theorem accepted_round_floor_cases (S : Setup V) (rho : NamedRun V)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.attest a) ta) :
    (∃ _he : rho.events[i]? = some (.tick source ta),
      a.round ≤ S.hc.round_of (S.E.slotOf ta)) ∨
    (∃ o : NamedObject V, ∃ _he : rho.events[i]? = some (.deliver source o ta),
      a.round ≤ S.hc.round_of (NamedRun.stateBefore S rho i source).st.core.s) := by
  have hpre : a ∉ (NamedRun.stateBefore S rho i source).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hacc.2.1
  have hpost : a ∈ (NamedRun.stateBefore S rho (i + 1) source).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | tick v t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inl ⟨he, ?_⟩
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he] at hpost
    rcases NamedReceiptCallsF1.tick_new_full_row_origin _ S.E S.hc S.cfg (S.node source)
        (NamedRun.stateBefore S rho i source).st (NamedRun.stateBefore S rho i source).record ta
        a hpre hpost with hem | ⟨B, _, hpre0, hpost0⟩
    · have hemit : NamedRun.emits S rho source (.attest a) ta := ⟨i, he, hem⟩
      obtain ⟨_, _, _, _, _, _, ht, _⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemit
      rw [ht, Proofs.HealingLemmas.round_of_slotOf_a S a.round]
    · exact block_new_round_floor S
        (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i source).st ta)
        B a hpre0 hpost0
  | deliver v o t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inr ⟨o, he, ?_⟩
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he] at hpost
    cases o with
    | block B => exact block_new_round_floor S _ B a hpre hpost
    | gfVote u => exact False.elim (hpre hpost)
    | attest incoming => exact new_row_round_floor S.hc _ incoming a hpre hpost

private theorem opening_slot_le_of_round_le (S : Setup V) {q : Round} {slot : Slot}
    (hq : q ≤ S.hc.round_of slot) : S.hc.opening_slot q ≤ slot := by
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_two; omega
  exact (Nat.le_div_iff_mul_le hR).mp hq

private theorem source_acceptance_opening_le (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.attest a) ta) :
    opening S.E S.hc a.round ≤ ta := by
  rcases accepted_round_floor_cases S rho hacc with ⟨he, hf⟩ | ⟨o, he, hf⟩
  · have ht0 : 0 ≤ ta := (sch.in_horizon _ (List.mem_of_getElem? he)).1
    exact (Protocol.proposal_time_mono S.E (opening_slot_le_of_round_le S hf)).trans
      (Protocol.proposal_time_slotOf_le S.E ht0)
  · have hclock0 : 0 ≤ (NamedRun.stateBefore S rho i source).st.core.t :=
      Proofs.NamedRuntime.stateBefore_clock_mono S rho sch.sorted
        (fun e he => (sch.in_horizon e he).1) source (Nat.zero_le i)
    have hup := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted he
      (sch.in_horizon _ (List.mem_of_getElem? he)).1 source
    have hslot := opening_slot_le_of_round_le S hf
    rw [stateBefore_slot_clock S rho i source] at hslot
    exact (Protocol.proposal_time_mono S.E hslot).trans
      ((Protocol.proposal_time_slotOf_le S.E hclock0).trans hup)

private theorem round_bounds_of_clock (S : Setup V) (q r : Round) (st : Protocol.NamedStore V)
    (hclock : st.core.s = S.E.slotOf st.core.t)
    (hlo : opening S.E S.hc q ≤ st.core.t) (hhi : st.core.t < opening S.E S.hc r) :
    q ≤ S.hc.round_of st.core.s ∧ S.hc.round_of st.core.s < r := by
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_two; omega
  have hslot := Protocol.slot_le_slotOf_of_proposal_time_le S.E hlo
  rw [← hclock] at hslot
  refine ⟨(Nat.le_div_iff_mul_le hR).mpr hslot, ?_⟩
  by_contra hn
  have hr : r ≤ S.hc.round_of st.core.s := Nat.le_of_not_gt hn
  have hcur : S.hc.opening_slot (S.hc.round_of st.core.s) ≤ st.core.s :=
    Nat.div_mul_le_self st.core.s S.hc.R
  have hro : S.hc.opening_slot r ≤ st.core.s := (Nat.mul_le_mul_right S.hc.R hr).trans hcur
  have ht0 : 0 ≤ st.core.t :=
    (Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot q)).trans hlo
  have hTslot : Protocol.proposal_time S.E st.core.s ≤ st.core.t := by
    rw [hclock]
    exact Protocol.proposal_time_slotOf_le S.E ht0
  exact (not_lt_of_ge ((Protocol.proposal_time_mono S.E hro).trans hTslot)) hhi

private theorem delivery_round_bounds (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {i : Nat} {reader : V} {o : NamedObject V} {td : Time}
    (q r : Round) (he : rho.events[i]? = some (.deliver reader o td))
    (hlo : opening S.E S.hc q ≤ td) (hhi : td < opening S.E S.hc r) :
    q ≤ S.hc.round_of (NamedRun.stateBefore S rho i reader).st.core.s ∧
      S.hc.round_of (NamedRun.stateBefore S rho i reader).st.core.s < r := by
  have hmem := List.mem_of_getElem? he
  have hr : reader ∈ rho.honest := sch.honest_only _ hmem
  have htick := sch.tick_total reader hr (opening S.E S.hc q)
    (Proofs.Optimistic.publicTime_proposal_time S (S.hc.opening_slot q))
    (Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot q))
    (hlo.trans (sch.in_horizon _ hmem).2)
  have hclock := tick_le_clock_before_delivery S rho sch he htick hlo
  have hup := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted he
    (sch.in_horizon _ hmem).1 reader
  exact round_bounds_of_clock S q r _ (stateBefore_slot_clock S rho i reader)
    hclock (hup.trans_lt hhi)

private theorem relay_call_input (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round) {i : Nat} {reader : V}
    {a : NamedAttestation V} {td : Time}
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td)
    (hlo : opening S.E S.hc a.round ≤ td) (hhi : td < opening S.E S.hc r) :
    ∃ input : Protocol.NamedStore V, Proofs.NamedStore.Coherent S.E S.cfg input ∧ Data td input ∧
      (a.round ≤ S.hc.round_of input.core.s ∧ S.hc.round_of input.core.s < r) ∧
      ∀ b : NamedAttestation V,
        b ∈ (Protocol.NamedAdmission.admit_row S.hc input a).sg_rows b.round →
        b ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows b.round := by
  rcases hcall.1 with hdirect | ⟨B, k, before, hF1⟩
  · rcases hdirect with ⟨t, he, hem⟩ | ⟨t, he⟩
    · have hemit : NamedRun.emits S rho reader (.attest a) t := ⟨i, he, hem⟩
      obtain ⟨j, hj, _, hrow, _, hround, htime, hawake⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemit
      have hij : j = i := by
        obtain ⟨_, hgetj⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨_, hgeti⟩ := List.getElem?_eq_some_iff.mp he
        exact (List.Nodup.getElem_inj_iff sch.nodup).mp (by rw [hgetj, hgeti])
      subst j
      have ht : t = td := handle_event_time S rho hcall he
      rcases htime with rfl
      rcases ht.symm with rfl
      let n := actionReadFrom S (NamedRun.stateBefore S rho i reader) a.round
      have hpre := (data_at_event S rho sch he reader).1
      have hd : Data (S.a a.round) n.st :=
        confirmation_data _ S _ _ _ (clock_data S _ _ _ le_rfl hpre)
      refine ⟨n.st, (Proofs.NamedOutageInputs.action_read_invariant S rho i reader a.round).1.1,
        hd, round_bounds_of_clock S a.round r n.st rfl hlo hhi, ?_⟩
      intro b hb
      rw [Proofs.NamedRuntime.stateBefore_tick S rho he, action_tick_store S reader _ a.round hawake]
      change b ∈ (Protocol.NamedAdmission.admit_row S.hc n.st
        (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
          S.E S.hc (S.node reader) n.st n.record).2.2).sg_rows b.round
      rwa [hrow]
    · have ht : t = td := handle_event_time S rho hcall he
      subst t
      refine ⟨(NamedRun.stateBefore S rho i reader).st,
        (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
        (data_at_event S rho sch he reader).1,
        delivery_round_bounds S rho sch a.round r he hlo hhi, ?_⟩
      intro b hb
      rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he]
      exact hb
  · have hbefore : Proofs.NamedStore.Coherent S.E S.cfg before ∧ Data td before ∧
        (a.round ≤ S.hc.round_of before.core.s ∧ S.hc.round_of before.core.s < r) := by
      rcases hF1.1 with ⟨t, he, rfl⟩ | ⟨t, he, hem, rfl⟩
      · have ht : t = td := handle_event_time S rho hcall he
        subst t
        exact ⟨(Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          (data_at_event S rho sch he reader).1,
          delivery_round_bounds S rho sch a.round r he hlo hhi⟩
      · have ht : t = td := handle_event_time S rho hcall he
        subst t
        refine ⟨NamedStore.coherent_clock S.E S.cfg _ td
          (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          clock_data S td _ td le_rfl (data_at_event S rho sch he reader).1, ?_⟩
        exact round_bounds_of_clock S a.round r _ rfl hlo hhi
    let input := Execution.NamedReceiptCalls.f1Input S before B k
    have hcore := NamedStore.coherent_process_block S.E S.hc S.cfg before B hbefore.1
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg input :=
      NamedAdmission.coherent_admit_rows S.E S.hc S.cfg _ (B.attestations.take k) hcore
    have hd : Data td input := rows_data S td _ (B.attestations.take k) hcore
      (core_block_data S td before B hbefore.2.1)
    have hround : a.round ≤ S.hc.round_of input.core.s ∧ S.hc.round_of input.core.s < r := by
      rw [(NamedReceiptCallsF1.actual_f1_clock S rho i reader B k a before hF1).2]
      exact hbefore.2.2
    refine ⟨input, hcoh, hd, hround, ?_⟩
    intro b hb
    apply block_call_rows_after_event S rho hF1.1 b
    rw [(NamedReceiptCallsF1.actual_carried_call S rho i reader B k a before hF1).2.2.2.2]
    exact NamedReceiptCallsF1.admit_rows_mem_mono S.hc _ (B.attestations.drop (k + 1)) b hb

private theorem window_bounds {eta r q : Round} (hq : q ∈ Protocol.latest_window eta r) :
    r - eta ≤ q ∧ q < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  refine ⟨Nat.le_add_right _ _, ?_⟩
  by_cases heta : eta ≤ r
  · have hsum : r - eta + eta = r := Nat.sub_add_cancel heta
    have hiEta : i < eta := by simpa only [Nat.min_eq_right heta] using hi
    calc
      r - eta + i < r - eta + eta := Nat.add_lt_add_left hiEta _
      _ = r := hsum
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge heta), Nat.zero_add]
    exact hi.trans_le (Nat.min_le_left r eta)

private theorem key_representative (S : Setup V) (input : Protocol.NamedStore V) (bound : Time)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg input) (hd : Data bound input)
    (a : NamedAttestation V) (key : Option BlockId)
    (hk : key ∈ Protocol.round_votes input.core a.erase) :
    ∃ b : NamedAttestation V, b ∈ input.sg_rows b.round ∧ b.round = a.round ∧
      b.val_index = a.val_index ∧ b.confirmed = key := by
  obtain ⟨erased, herased, hval, hkey⟩ := Proofs.Optimistic.mem_round_votes.mp hk
  obtain ⟨b, hb, he⟩ := pool_full_witness S input hcoh a.round erased herased
  have hr : b.round = a.round := (hd.2 a.round b hb).1
  refine ⟨b, by simpa only [hr] using hb, hr, ?_, ?_⟩
  · exact (congrArg CombinedAttestation.val_index he).trans hval
  · exact (congrArg CombinedAttestation.confirmed he).trans hkey

/-- The receiver keeps full representatives, which can differ from the
incoming full payload. The conclusion records SG keys, not full identity. -/
private def Outcome (st : Protocol.NamedStore V) (a : NamedAttestation V) : Prop :=
  (∃ vote : NamedAttestation V, vote ∈ st.sg_rows vote.round ∧ vote.round = a.round ∧
    vote.val_index = a.val_index ∧ vote.confirmed = a.confirmed) ∨
  ∃ left right : NamedAttestation V,
    left ∈ st.sg_rows left.round ∧ right ∈ st.sg_rows right.round ∧
    left.round = a.round ∧ right.round = a.round ∧
    left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
    left.confirmed ≠ right.confirmed

private theorem call_vote_or_equiv (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round)
    {j : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (hcall : NamedRun.actualHandlesAt S rho j reader (.attest a) td)
    (hlo : opening S.E S.hc a.round ≤ td) (hhi : td < opening S.E S.hc r)
    (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r) :
    Outcome (NamedRun.stateBefore S rho (j + 1) reader).st a := by
  obtain ⟨input, hcoh, hd, hbounds, hpost⟩ := relay_call_input S rho sch r hcall hlo hhi
  have hw := window_bounds hwindow
  have hexp : ¬ a.round < S.hc.round_of input.core.s - S.hc.η_SG := by
    apply Nat.not_lt.mpr
    exact (Nat.sub_le_sub_right hbounds.2.le S.hc.η_SG).trans hw.1
  have hfuture : ¬ S.hc.round_of input.core.s < a.round := Nat.not_lt.mpr hbounds.1
  have held_to_post (b : NamedAttestation V) (hb : b ∈ input.sg_rows b.round) :
      b ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows b.round :=
    hpost b (NamedReceiptCallsF1.admit_row_mem_mono S.hc input a b hb)
  by_cases hdup : a.confirmed ∈ Protocol.round_votes input.core a.erase
  · obtain ⟨vote, hvote, hr, hv, hk⟩ :=
      key_representative S input td hcoh hd a a.confirmed hdup
    exact Or.inl ⟨vote, held_to_post vote hvote, hr, hv, hk⟩
  · by_cases hcap : (Protocol.round_votes input.core a.erase).card = 2
    · have htwo : 1 < (Protocol.round_votes input.core a.erase).card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
      obtain ⟨left, hl, hrl, hvl, hkl⟩ := key_representative S input td hcoh hd a x hx
      obtain ⟨right, hr, hrr, hvr, hkr⟩ := key_representative S input td hcoh hd a y hy
      refine Or.inr ⟨left, right, held_to_post left hl, held_to_post right hr,
        hrl, hrr, hvl, hvr, ?_⟩
      intro heq
      exact hxy (hkl.symm.trans (heq.trans hkr))
    · have hguard : ¬ (a.round < S.hc.round_of input.core.s - S.hc.η_SG ∨
          S.hc.round_of input.core.s < a.round ∨
          a.confirmed ∈ Protocol.round_votes input.core a.erase ∨
          (Protocol.round_votes input.core a.erase).card = 2) := by
        simp only [not_or]
        exact ⟨hexp, hfuture, hdup, hcap⟩
      have hpre : a.erase ∉ input.core.sg_pool a.round := by
        intro ha
        exact hdup (Proofs.Optimistic.mem_round_votes.mpr ⟨a.erase, ha, rfl, rfl⟩)
      have hnew : a.erase ∈ (Protocol.on_sg_vote S.hc input.core a.erase).sg_pool a.round := by
        dsimp only [Protocol.on_sg_vote]
        simp only [show a.erase.round = a.round from rfl,
          show a.erase.confirmed = a.confirmed from rfl]
        rw [if_neg hguard]
        simp [Protocol.Store.sg_pool]
      have ha := hpost a (NamedAdmission.admitted_original_row S.hc input a hpre hnew)
      exact Or.inl ⟨a, ha, rfl, rfl, rfl⟩


private theorem early_g1_delay_eq_g0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 + S.E.Δ = early S.E S.hc r .g0 := by
  unfold early Phase.earlyOffset
  ring

/-- G0 twin of `early_g1_lt_opening`. -/
private theorem early_g0_lt_opening (S : Setup V) (r : Round) :
    early S.E S.hc r .g0 < opening S.E S.hc r := by
  unfold early Phase.earlyOffset
  change opening S.E S.hc r + (-3 : Time) * S.E.Δ < opening S.E S.hc r
  have hneg : (-3 : Time) * S.E.Δ < 0 :=
    Int.mul_neg_of_neg_of_pos (by norm_num) S.E.Δ_pos
  calc
    opening S.E S.hc r + (-3 : Time) * S.E.Δ < opening S.E S.hc r + 0 :=
      (add_lt_add_iff_left _).2 hneg
    _ = opening S.E S.hc r := add_zero _

/-- G0 twin of `early_g1_le_domain_g1` (domain offset for `.g0` is `+1`, not
`0`, so this is a strict schedule inequality rather than the `.g1` identity;
it is still exactly what the `.g0` forward relay needs). -/
private theorem early_g0_le_domain_g0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g0 ≤ domain S.E S.hc r .g0 := by
  simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

/-- G0 twin of `held_projection_raw_after_event` (the `.g1`-early one above):
the original full representative and its unchanged first stamp are
transported from this event's own post-index to the target strict read, at
the `.g0` early cutoff and `.g0` domain read. -/
private theorem held_projection_raw_after_event_g0 (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round) (reader sender : V)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < early S.E S.hc r .g0) (b : NamedAttestation V)
    (hb : b ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows b.round)
    (hwindow : b.round ∈ Protocol.latest_window S.hc.η_SG r) (hval : b.val_index = sender) :
    let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g0) reader
    Protocol.sgVote b.erase ∈ DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
      S.hc.η_SG r (early S.E S.hc r .g0) sender := by
  let cut := domain S.E S.hc r .g0
  let n := NamedRun.stateBeforeTime S rho cut reader
  have hpostData := (data_at_event S rho sch he reader).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hpostData.2 b.round b hb
  have hcut : e.time < cut := ht.trans_le (early_g0_le_domain_g0 S r)
  have hindex := post_index_le_strict_filter_length rho sch.sorted cut he hcut
  obtain ⟨hretained, hstampRetained⟩ :=
    Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader hindex hb
  have hread : NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho (rho.events.filter (fun e => decide (e.time < cut))).length :=
    congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
      (strict_filter_eq_take rho sch.sorted cut)
  have hheld : b ∈ n.st.sg_rows b.round := by simpa only [n, hread] using hretained
  have hreceipt : n.st.core.timestamp_sg_vote (Protocol.sgVote b.erase) = some (stamp : Stamp) := by
    simpa only [n, hread] using hstampRetained.trans hstamp
  have hoccur : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote b.erase))
      (early S.E S.hc r .g0) = true := by
    simp only [hreceipt, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt ht)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  have hpool := NamedAdmission.pool_view_mem n.st hcoh.2.2.2.1 b hheld
  have hsg : Protocol.sgVote b.erase ∈ n.st.core.toHealing.gradeView.sg_votes b.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ?_, hval, hoccur⟩
  exact ⟨b.round, List.mem_toFinset.mpr hwindow, hsg⟩


/-- G0/G1 twin of `late_g1_delay_eq_g2`. -/
private theorem late_g0_delay_eq_g1 (S : Setup V) (r : Round) :
    late S.E S.hc r .g0 + S.E.Δ = late S.E S.hc r .g1 := by
  unfold late Phase.lateOffset
  ring

/-- G1 twin of `late_g1_le_domain_g1` used elsewhere for the read side: since
`.g1`'s late offset (`-2`) differs from its domain offset (`0`), unlike the
`.g2` original where `late_g2_eq_domain_g2` is exact equality, this is a
strict schedule inequality, which is exactly what the `.g1`-late relay needs
in place of the `.g2` identity. -/
private theorem late_g1_le_domain_g1 (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 ≤ domain S.E S.hc r .g1 := by
  simp only [late, domain, Phase.lateOffset, Phase.domainOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

/-- G1 twin of `late_g2_lt_opening`. -/
private theorem late_g1_lt_opening (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 < opening S.E S.hc r := by
  unfold late Phase.lateOffset
  change opening S.E S.hc r + (-2 : Time) * S.E.Δ < opening S.E S.hc r
  have hneg : (-2 : Time) * S.E.Δ < 0 :=
    Int.mul_neg_of_neg_of_pos (by norm_num) S.E.Δ_pos
  calc
    opening S.E S.hc r + (-2 : Time) * S.E.Δ < opening S.E S.hc r + 0 :=
      (add_lt_add_iff_left _).2 hneg
    _ = opening S.E S.hc r := add_zero _

/-- G1 twin of `held_projection_raw_after_event` (the `.g2`-late one above),
at the `.g1` late cutoff and `.g1` domain read. Since `domain`'s offset for
`.g1` is `0`, the same `change`/`zero_mul` unfolding the `.g2` original used
for its own domain offset applies unchanged here. -/
private theorem held_projection_raw_after_event_g1 (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round) (reader sender : V)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < late S.E S.hc r .g1) (b : NamedAttestation V)
    (hb : b ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows b.round)
    (hwindow : b.round ∈ Protocol.latest_window S.hc.η_SG r) (hval : b.val_index = sender) :
    let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) reader
    Protocol.sgVote b.erase ∈ DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
      S.hc.η_SG r (late S.E S.hc r .g1) sender := by
  let cut := domain S.E S.hc r .g1
  let n := NamedRun.stateBeforeTime S rho cut reader
  have hpostData := (data_at_event S rho sch he reader).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hpostData.2 b.round b hb
  have hcut : e.time < cut := ht.trans_le (late_g1_le_domain_g1 S r)
  have hindex := post_index_le_strict_filter_length rho sch.sorted cut he hcut
  obtain ⟨hretained, hstampRetained⟩ :=
    Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader hindex hb
  have hread : NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho (rho.events.filter (fun e => decide (e.time < cut))).length :=
    congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
      (strict_filter_eq_take rho sch.sorted cut)
  have hheld : b ∈ n.st.sg_rows b.round := by simpa only [n, hread] using hretained
  have hreceipt : n.st.core.timestamp_sg_vote (Protocol.sgVote b.erase) = some (stamp : Stamp) := by
    simpa only [n, hread] using hstampRetained.trans hstamp
  have hoccur : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote b.erase))
      (late S.E S.hc r .g1) = true := by
    simp only [hreceipt, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt ht)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  have hpool := NamedAdmission.pool_view_mem n.st hcoh.2.2.2.1 b hheld
  have hsg : Protocol.sgVote b.erase ∈ n.st.core.toHealing.gradeView.sg_votes b.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ?_, hval, hoccur⟩
  exact ⟨b.round, List.mem_toFinset.mpr hwindow, hsg⟩


private theorem accepted_sg_vote_or_equiv_at_g0_of_relay_local
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (core : NamedAdmissibleCore S rho)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.attest a) ta)
    (hsourceCut : ta < early S.E S.hc r .g1)
    (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r)
    (relay : ∀ reader ∈ rho.honest,
      NamedReceipt.processed
          (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false →
        ∃ td, ta ≤ td ∧ td < early S.E S.hc r .g0 ∧
          ∃ j : Nat, NamedRun.actualHandlesAt S rho j reader (.attest a) td) :
    ∀ reader ∈ rho.honest,
      let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g0) reader
      let raw := DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g0) a.val_index
      Protocol.sgVote a.erase ∈ raw ∨
        ∃ left ∈ raw, ∃ right ∈ raw,
          left.round = a.round ∧ right.round = a.round ∧
          left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
          left.confirmed ≠ right.confirmed := by
  obtain ⟨sourceEvent, hsourceEvent, -, hsourceTime⟩ := hacc.1.2
  have htaEarly : ta < early S.E S.hc r .g0 :=
    hsourceCut.trans (by
      rw [← early_g1_delay_eq_g0 S r]
      exact lt_add_of_pos_right _ S.E.Δ_pos)
  have hsourceFloor :=
    source_acceptance_opening_le S rho core.toNamedScheduleWellFormed hacc
  intro reader hreader
  by_cases hskip : a ∈
      (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows a.round
  · apply Or.inl
    exact held_projection_raw_after_event_g0 S rho
      core.toNamedScheduleWellFormed r reader a.val_index hsourceEvent
      (by simpa only [hsourceTime] using htaEarly) a hskip hwindow rfl
  · have hmissing : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false := by
      simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
    obtain ⟨td, hlo, htdEarly, j, hcall⟩ := relay reader hreader hmissing
    have htdOpen : td < opening S.E S.hc r :=
      htdEarly.trans (early_g0_lt_opening S r)
    have hout := call_vote_or_equiv S rho core.toNamedScheduleWellFormed r
      hcall (hsourceFloor.trans hlo) htdOpen hwindow
    obtain ⟨e, he, _, het⟩ := hcall.2
    have heEarly : e.time < early S.E S.hc r .g0 := by
      simpa only [het] using htdEarly
    rcases hout with ⟨vote, hvote, hround, hval, hkey⟩ |
      ⟨left, right, hleft, hright, hlround, hrround, hlval, hrval, hkeys⟩
    · have hraw := held_projection_raw_after_event_g0 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly vote
        hvote (by simpa only [hround] using hwindow) hval
      have hproj : Protocol.sgVote vote.erase = Protocol.sgVote a.erase := by
        change Protocol.SGVote.mk vote.val_index vote.round vote.confirmed =
          Protocol.SGVote.mk a.val_index a.round a.confirmed
        rw [hval, hround, hkey]
      exact Or.inl (by simpa only [hproj] using hraw)
    · have hlraw := held_projection_raw_after_event_g0 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly left
        hleft (by simpa only [hlround] using hwindow) hlval
      have hrraw := held_projection_raw_after_event_g0 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly right
        hright (by simpa only [hrround] using hwindow) hrval
      exact Or.inr ⟨Protocol.sgVote left.erase, hlraw,
        Protocol.sgVote right.erase, hrraw, hlround, hrround, hlval, hrval,
        hkeys⟩

theorem accepted_sg_vote_or_equiv_at_g1_late_of_relay_local
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (core : NamedAdmissibleCore S rho)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.attest a) ta)
    (hsourceCut : ta < late S.E S.hc r .g0)
    (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r)
    (relay : ∀ reader ∈ rho.honest,
      NamedReceipt.processed
          (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false →
        ∃ td, ta ≤ td ∧ td < late S.E S.hc r .g1 ∧
          ∃ j : Nat, NamedRun.actualHandlesAt S rho j reader (.attest a) td) :
    ∀ reader ∈ rho.honest,
      let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) reader
      let raw := DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
        S.hc.η_SG r (late S.E S.hc r .g1) a.val_index
      Protocol.sgVote a.erase ∈ raw ∨
        ∃ left ∈ raw, ∃ right ∈ raw,
          left.round = a.round ∧ right.round = a.round ∧
          left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
          left.confirmed ≠ right.confirmed := by
  obtain ⟨sourceEvent, hsourceEvent, -, hsourceTime⟩ := hacc.1.2
  have htaLate : ta < late S.E S.hc r .g1 :=
    hsourceCut.trans (by
      rw [← late_g0_delay_eq_g1 S r]
      exact lt_add_of_pos_right _ S.E.Δ_pos)
  have hsourceFloor :=
    source_acceptance_opening_le S rho core.toNamedScheduleWellFormed hacc
  intro reader hreader
  by_cases hskip : a ∈
      (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows a.round
  · apply Or.inl
    exact held_projection_raw_after_event_g1 S rho
      core.toNamedScheduleWellFormed r reader a.val_index hsourceEvent
      (by simpa only [hsourceTime] using htaLate) a hskip hwindow rfl
  · have hmissing : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false := by
      simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
    obtain ⟨td, hlo, htdLate, j, hcall⟩ := relay reader hreader hmissing
    have htdOpen : td < opening S.E S.hc r :=
      htdLate.trans (late_g1_lt_opening S r)
    have hout := call_vote_or_equiv S rho core.toNamedScheduleWellFormed r
      hcall (hsourceFloor.trans hlo) htdOpen hwindow
    obtain ⟨e, he, _, het⟩ := hcall.2
    have heLate : e.time < late S.E S.hc r .g1 := by
      simpa only [het] using htdLate
    rcases hout with ⟨vote, hvote, hround, hval, hkey⟩ |
      ⟨left, right, hleft, hright, hlround, hrround, hlval, hrval, hkeys⟩
    · have hraw := held_projection_raw_after_event_g1 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heLate vote
        hvote (by simpa only [hround] using hwindow) hval
      have hproj : Protocol.sgVote vote.erase = Protocol.sgVote a.erase := by
        change Protocol.SGVote.mk vote.val_index vote.round vote.confirmed =
          Protocol.SGVote.mk a.val_index a.round a.confirmed
        rw [hval, hround, hkey]
      exact Or.inl (by simpa only [hproj] using hraw)
    · have hlraw := held_projection_raw_after_event_g1 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heLate left
        hleft (by simpa only [hlround] using hwindow) hlval
      have hrraw := held_projection_raw_after_event_g1 S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heLate right
        hright (by simpa only [hrround] using hwindow) hrval
      exact Or.inr ⟨Protocol.sgVote left.erase, hlraw,
        Protocol.sgVote right.erase, hrraw, hlround, hrround, hlval, hrval,
        hkeys⟩

end PrivateRelayKernel

abbrev phaseRead (S : Setup V) (rho : NamedRun V)
    (r : Round) (p : Phase) (v : V) : NamedNodeState V :=
  NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v

/-- The two fixed relay facts used by cross-reader G2-to-G1 transport.
Each field asks for the relevant phase cutoff to be inside the finite run.
The early hop carries attestations and referenced block bodies. The late
hop carries attestations back to the G2 reader. -/
structure TwoCutoffDelivery
    (S : Setup V) (rho : NamedRun V) (r : Round) : Prop where
  earlyAttest : ∀ source ∈ rho.honest, ∀ i a t,
    NamedRun.acceptsAt S rho i source (.attest a) t →
    t < early S.E S.hc r .g2 → ∀ target ∈ rho.honest,
    NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) target).st (.attest a) = false →
    early S.E S.hc r .g1 ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < early S.E S.hc r .g1 ∧
        ∃ j, NamedRun.actualHandlesAt S rho j target (.attest a) t'
  lateAttest : ∀ source ∈ rho.honest, ∀ i a t,
    NamedRun.acceptsAt S rho i source (.attest a) t →
    t < late S.E S.hc r .g1 → ∀ target ∈ rho.honest,
    NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) target).st (.attest a) = false →
    late S.E S.hc r .g2 ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < late S.E S.hc r .g2 ∧
        ∃ j, NamedRun.actualHandlesAt S rho j target (.attest a) t'

/-- The G1-to-G0 twin of `TwoCutoffDelivery`. -/
structure G1G0TwoCutoffDelivery
    (S : Setup V) (rho : NamedRun V) (r : Round) : Prop where
  earlyAttest : ∀ source ∈ rho.honest, ∀ i a t,
    NamedRun.acceptsAt S rho i source (.attest a) t →
    t < early S.E S.hc r .g1 → ∀ target ∈ rho.honest,
    NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) target).st (.attest a) = false →
    early S.E S.hc r .g0 ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < early S.E S.hc r .g0 ∧
        ∃ j, NamedRun.actualHandlesAt S rho j target (.attest a) t'
  lateAttest : ∀ source ∈ rho.honest, ∀ i a t,
    NamedRun.acceptsAt S rho i source (.attest a) t →
    t < late S.E S.hc r .g0 → ∀ target ∈ rho.honest,
    NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) target).st (.attest a) = false →
    late S.E S.hc r .g1 ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < late S.E S.hc r .g1 ∧
        ∃ j, NamedRun.actualHandlesAt S rho j target (.attest a) t'

private theorem early_g2_add_delta_eq_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 + S.E.Δ = early S.E S.hc r .g1 := by
  unfold early Phase.earlyOffset
  ring

private theorem late_g1_add_delta_eq_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 + S.E.Δ = late S.E S.hc r .g2 := by
  unfold late Phase.lateOffset
  ring

private theorem early_g1_add_delta_eq_g0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 + S.E.Δ = early S.E S.hc r .g0 := by
  unfold early Phase.earlyOffset
  ring

private theorem late_g0_add_delta_eq_g1 (S : Setup V) (r : Round) :
    late S.E S.hc r .g0 + S.E.Δ = late S.E S.hc r .g1 := by
  unfold late Phase.lateOffset
  ring

private theorem domain_g1_le_domain_g0 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
  simp only [domain, Phase.domainOffset]
  exact Int.add_le_add_left
      (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

private theorem domain_g2_add_delta_eq_g1 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 + S.E.Δ = domain S.E S.hc r .g1 := by
  unfold domain Phase.domainOffset
  ring

private theorem domain_g1_add_delta_eq_g0 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 + S.E.Δ = domain S.E S.hc r .g0 := by
  unfold domain Phase.domainOffset
  ring

private theorem early_g2_le_domain_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ domain S.E S.hc r .g2 := by
  simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
  linarith [S.E.Δ_pos]

private theorem early_g1_le_domain_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ domain S.E S.hc r .g1 := by
  simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
  linarith [S.E.Δ_pos]

private theorem early_g0_le_late_g0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g0 ≤ late S.E S.hc r .g0 := by
  simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
  exact le_rfl

private theorem early_g1_public (S : Setup V) (r : Round) (hr : 0 < r) :
    PublicTime S (early S.E S.hc r .g1) := by
  have hslots : 2 ≤ r * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hr)
  have hcoef : 4 ≤ 4 * (r * S.hc.R) := by
    calc
      4 ≤ 4 * 2 := by decide
      _ ≤ 4 * (r * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (r * S.hc.R) - 4, ?_⟩
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

private theorem late_g0_public (S : Setup V) (r : Round) (hr : 0 < r) :
    PublicTime S (late S.E S.hc r .g0) := by
  have hslots : 2 ≤ r * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hr)
  have hcoef : 3 ≤ 4 * (r * S.hc.R) := by
    calc
      3 ≤ 4 * 2 := by decide
      _ ≤ 4 * (r * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (r * S.hc.R) - 3, ?_⟩
  unfold late opening Phase.lateOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

private theorem late_g2_eq_domain_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g2 = domain S.E S.hc r .g2 := by
  simp only [late, domain, Phase.lateOffset, Phase.domainOffset]

omit [Fintype V] in
private theorem named_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hBC
      subst B
      exact hAB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC
      rcases hBC with rfl | hparent
      · exact hAB
      · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (ih hparent)

private theorem finalized_justification_ancestor
    (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ C : NamedBlock V, ∃ D : NamedBlock V,
      NamedBlock.Preceq D C ∧
      (C = .genesis ∨ NamedBlock.Preceq D C.parent) ∧
      (Protocol.derive_named E cfg D).J =
        (Protocol.derive_named E cfg C).F ∧
      (Protocol.derive_named E cfg D).h_j =
        (Protocol.derive_named E cfg C).h_F := by
  intro C
  induction C with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, Or.inl rfl, rfl, rfl⟩
  | node parent slot root votes support rows proposer ih =>
      let C : NamedBlock V :=
        .node parent slot root votes support rows proposer
      let folded := Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg parent) C.erase C.attestations
      have hstate : Protocol.derive_named E cfg C =
          Protocol.process_height_events E cfg folded := rfl
      have hfields := NamedDerivationGeometry.fold_context_fields
        (Protocol.TimeoutBinding.targeted V) C.attestations
        { Protocol.derive_named E cfg parent with s := C.erase.slot }
      have hfoldJ : folded.J =
          (Protocol.derive_named E cfg parent).J := hfields.2.2.2.1
      have hfoldHj : folded.h_j =
          (Protocol.derive_named E cfg parent).h_j := hfields.2.2.2.2.1
      have hfoldF : folded.F =
          (Protocol.derive_named E cfg parent).F := hfields.2.2.2.2.2.1
      have hfoldHf : folded.h_F =
          (Protocol.derive_named E cfg parent).h_F :=
        hfields.2.2.2.2.2.2
      have hafter : ∃ D : NamedBlock V,
          NamedBlock.Preceq D C ∧ NamedBlock.Preceq D parent ∧
          (Protocol.derive_named E cfg D).J =
            (Protocol.afterFin E folded).F ∧
          (Protocol.derive_named E cfg D).h_j =
            (Protocol.afterFin E folded).h_F := by
        rw [Protocol.afterFin_F, Protocol.afterFin_h_F]
        split_ifs
        · refine ⟨parent, ?_, Proofs.NamedAncestry.named_self parent, ?_, ?_⟩
          · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
              (Proofs.NamedAncestry.named_self parent)
          · exact hfoldJ.symm
          · exact hfoldHj.symm
        · obtain ⟨D, hDC, -, hDJ, hDh⟩ := ih
          refine ⟨D, named_trans hDC ?_, hDC, ?_, ?_⟩
          · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
              (Proofs.NamedAncestry.named_self parent)
          · exact hDJ.trans hfoldF.symm
          · exact hDh.trans hfoldHf.symm
      rw [hstate, Protocol.process_height_events_eq]
      split_ifs <;>
        exact ⟨hafter.choose, hafter.choose_spec.1,
          Or.inr hafter.choose_spec.2.1, hafter.choose_spec.2.2.1,
          hafter.choose_spec.2.2.2⟩

private theorem gf_fields (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    let next := Protocol.on_goldfish_vote_checked E st u
    next.T = st.T ∧ next.σ = st.σ ∧ next.F = st.F ∧
      next.J = st.J ∧ next.h_j = st.h_j ∧ next.h_max = st.h_max := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem gf_fold_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let next := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    next.T = st.T ∧ next.σ = st.σ ∧ next.F = st.F ∧
      next.J = st.J ∧ next.h_j = st.h_j ∧ next.h_max = st.h_max := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons u votes ih =>
      have rest := ih (Protocol.on_goldfish_vote_checked E st u)
      have one := gf_fields E st u
      exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
        rest.2.2.1.trans one.2.2.1,
        rest.2.2.2.1.trans one.2.2.2.1,
        rest.2.2.2.2.1.trans one.2.2.2.2.1,
        rest.2.2.2.2.2.trans one.2.2.2.2.2⟩

private theorem absorb_finality_step (U afterJ : Protocol.Store V)
    (sigma : Protocol.ChainState V)
    (hF : afterJ.F = U.F) (hsigma : afterJ.σ = U.σ)
    (hT : afterJ.T = U.T)
    (hmax : afterJ.h_max = max U.h_max sigma.h)
    (hnot : ¬ Block.Preceq sigma.F U.F)
    (hviable : sigma.F ∈ Protocol.viable_tree U.σ U.F
      (max U.h_max sigma.h) U.T)
    (hJ : Block.Preceq sigma.F afterJ.J) :
    Block.Preceq sigma.F
      (if Block.prec afterJ.F sigma.F &&
          Block.preceq sigma.F afterJ.J &&
          decide (sigma.F ∈ Protocol.viable_tree afterJ.σ afterJ.F
            afterJ.h_max afterJ.T) then
        ({ afterJ with F := sigma.F } : Protocol.Store V)
      else afterJ).F := by
  have hUF : Block.Preceq U.F sigma.F :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hviable).1).2
  have hne : U.F ≠ sigma.F := by
    intro heq
    apply hnot
    rw [← heq]
    exact Block.preceq_self _
  have hprec : Block.prec U.F sigma.F = true := by
    change (!decide (U.F = sigma.F) && Block.preceq U.F sigma.F) = true
    rw [show decide (U.F = sigma.F) = false by simp [hne]]
    simpa only [Bool.not_false, Bool.true_and] using hUF
  have hguard :
      (Block.prec afterJ.F sigma.F &&
        Block.preceq sigma.F afterJ.J &&
        decide (sigma.F ∈ Protocol.viable_tree afterJ.σ afterJ.F
          afterJ.h_max afterJ.T)) = true := by
    rw [hF, hsigma, hT, hmax]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hprec, hJ⟩, hviable⟩
  rw [if_pos hguard]
  exact Block.preceq_self _

/-- A fresh accepted named carrier makes its own finalized checkpoint local.
This is the named B10 instance needed by the one-hop finality relay. -/
private theorem fresh_receipt_absorbs_finality
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hsb : SlashableBound S rho) {i : Nat} {target : V}
    (htarget : target ∈ rho.honest) (B : NamedBlock V)
    (hBscope : NamedRun.blockInRun S rho B)
    (before : Protocol.NamedStore V)
    (hcall : Execution.NamedReceiptCalls.blockCallAt
      S rho i target B before)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S before B).core.T)
    (hfloor : Block.Preceq
      (NamedRun.stateBefore S rho i target).st.core.F
      (Protocol.derive_named S.E S.cfg B).F) :
    Block.Preceq (Protocol.derive_named S.E S.cfg B).F
      (Execution.NamedReceiptCalls.postCore S before B).core.F := by
  open Execution.NamedReceiptCalls in
  let sigma := Protocol.derive_named S.E S.cfg B
  rcases finalized_justification_ancestor S.E S.cfg B with
    ⟨A, hAB, hAcase, hAJ, hAh⟩
  rcases hAcase with hgen | hAparent
  · subst B
    change Block.Preceq Block.genesis _
    exact Protocol.preceq_genesis _
  · have hco : Proofs.NamedStore.Coherent S.E S.cfg before :=
      (Proofs.NamedReceiptCallsBase.block_call_before_invariant S rho hcall).1.1
    have hparent : B.parent ∈ before.bodies := by
      by_contra hn
      have hsame :
          (Execution.NamedReceiptCalls.postCore S before B).core =
            before.core := by
        simp only [Execution.NamedReceiptCalls.postCore,
          Protocol.NamedStore.process_block_core, if_pos hn]
      exact hnew (hsame ▸ hpost)
    have hAheld : A ∈ before.bodies :=
      NamedOutageHistory.ViabilityHistoryTime.ancestor_body_mem
        hco.2.2.1 hparent hAparent
    have hinputF : before.core.F =
        (NamedRun.stateBefore S rho i target).st.core.F := by
      rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩ <;> rfl
    have hfloorBefore : Block.Preceq before.core.F sigma.F := by
      rw [hinputF]
      exact hfloor
    have hfacts :
        (∀ D ∈ before.bodies, NamedRun.blockInRun S rho D) ∧
        Internal.NamedNoHighJustifications S.E S.cfg before ∧
        Proofs.Bridges.NamedProvenance S before ∧
        (∃ D ∈ before.bodies,
          (Protocol.derive_named S.E S.cfg D).h =
            before.core.h_max) := by
      rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩
      · refine ⟨?_, NamedJustificationBound.noHighJustifications_stateBefore
            S rho i target,
          Proofs.Bridges.namedProvenance_stateBefore S rho i target,
          Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho i target⟩
        intro D hD
        exact Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hD
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro D hD
          exact Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hD
        · simpa only [Protocol.NamedStore.setClock] using
            (NamedJustificationBound.noHighJustifications_stateBefore
              S rho i target)
        · simpa only [Protocol.NamedStore.setClock] using
            (Proofs.Bridges.namedProvenance_stateBefore S rho i target)
        · simpa only [Protocol.NamedStore.setClock] using
            (Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho i target)
    have hjust : Internal.NamedJustifiedAt S.E S.cfg A sigma.F sigma.h_F :=
      ⟨hAJ, hAh⟩
    have hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg B sigma.F sigma.h_F :=
      ⟨rfl, rfl⟩
    let stored : Protocol.Store V := { before.core with
      σ := fun X => if X = B.erase then
        Protocol.named_transition S.E S.cfg
          (before.core.σ B.erase.parent) B
        else before.core.σ X
      T := insert B.erase before.core.T
      timestamp_block := fun X => if X = B.erase then
        some (before.core.t : Stamp) else before.core.timestamp_block X }
    let U := B.gf_votes.foldl
      (Protocol.on_goldfish_vote_checked S.E) stored
    let afterMax : Protocol.Store V :=
      { U with h_max := max U.h_max sigma.h }
    let afterJ : Protocol.Store V :=
      if Block.preceq afterMax.F sigma.J &&
          decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
            Protocol.HeightId.mk sigma.h_j sigma.J.root) then
        { afterMax with J := sigma.J, h_j := sigma.h_j }
      else afterMax
    have hderived :=
      NamedOutageHistory.GuardProofsTime.fresh_receipt_derived_and_admitted
        S before B hco hnew hpost
    change U.σ B.erase = sigma ∧ Block.Preceq U.F B.erase at hderived
    have hfields := gf_fold_fields S.E stored B.gf_votes
    have hUT : U.T = insert B.erase before.core.T := hfields.1
    have hUsigma : U.σ = stored.σ := hfields.2.1
    have hUF : U.F = before.core.F := hfields.2.2.1
    have hUJ : U.J = before.core.J := hfields.2.2.2.1
    have hUhj : U.h_j = before.core.h_j := hfields.2.2.2.2.1
    have hUmax : U.h_max = before.core.h_max := hfields.2.2.2.2.2
    have hpostEq :
        (Execution.NamedReceiptCalls.postCore S before B).core =
          Protocol.update_finality U (U.σ B.erase) :=
      NamedReceiptCallsGF.post_core_stored S before B hnew hpost
    have htreeA : A.erase ∈ before.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hAheld
    have hFmemBefore : sigma.F ∈ before.core.T := by
      rw [← hAJ]
      exact NamedDerivationGeometry.core_ancestor_mem S.E S.cfg before hco
        htreeA
        (NamedDerivationGeometry.derive_named_anchors_preceq
          S.E S.cfg A).2
    have hFmemU : sigma.F ∈ U.T := by
      rw [hUT]
      exact Finset.mem_insert_of_mem hFmemBefore
    have hfloorU : Block.Preceq U.F sigma.F := by
      rw [hUF]
      exact hfloorBefore
    have hupgrade : Block.Preceq sigma.F before.core.J :=
      StoreFinality.upgrade hfacts.2.1 hfacts.2.2.1 hAheld hjust hsb
        core.toNamedRootCollisionFree hBscope hfacts.1 hfin
    have hafterJ : Block.Preceq sigma.F afterJ.J := by
      by_cases hg :
          (Block.preceq afterMax.F sigma.J &&
            decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
              Protocol.HeightId.mk sigma.h_j sigma.J.root)) = true
      · have horder :=
          NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
        have hFJ := horder.finalized_preceq_justified
        simpa only [afterJ, hg, if_true] using hFJ
      · have hgFalse :
            (Block.preceq afterMax.F sigma.J &&
              decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
                Protocol.HeightId.mk sigma.h_j sigma.J.root)) = false :=
          Bool.eq_false_of_not_eq_true hg
        have hafter : afterJ.J = afterMax.J := by
          simp only [afterJ, hgFalse, Bool.false_eq_true, if_false]
        rw [hafter]
        change Block.Preceq sigma.F U.J
        rw [hUJ]
        exact hupgrade
    have hviable : sigma.F ∈ Protocol.viable_tree U.σ U.F
        (max U.h_max sigma.h) U.T := by
      simp only [Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq]
      refine ⟨⟨hFmemU, hfloorU⟩, ?_⟩
      by_cases hlow : max U.h_max sigma.h - 1 ≤ sigma.h
      · refine ⟨B.erase, ?_, ?_, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_self _ _
        · exact
            (NamedDerivationGeometry.derive_named_anchors_preceq
              S.E S.cfg B).1
        · rw [hderived.1]
          exact hlow
      · obtain ⟨M, hMheld, hMheight⟩ := hfacts.2.2.2
        have hMraw : M.erase ∈ before.core.T := by
          rw [hco.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hMheld
        have hMne : M.erase ≠ B.erase := by
          intro heq
          exact hnew (heq ▸ hMraw)
        have hmaxEq : max U.h_max sigma.h = U.h_max := by
          by_cases hle : sigma.h ≤ U.h_max
          · exact Nat.max_eq_left hle
          · exfalso
            apply hlow
            rw [Nat.max_eq_right (Nat.le_of_not_ge hle)]
            exact Nat.sub_le _ _
        have hheight : sigma.h_F <
            (Protocol.derive_named S.E S.cfg M).h := by
          have hchain :=
            NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
          have horder := hchain.finalized_below_height
          change sigma.h_F < sigma.h at horder
          have hs : sigma.h < max U.h_max sigma.h - 1 :=
            Nat.lt_of_not_ge hlow
          have hout : sigma.h_F < U.h_max := by
            rw [hmaxEq] at hs
            exact lt_of_lt_of_le (lt_trans horder hs) (Nat.sub_le _ _)
          rw [hMheight, ← hUmax]
          exact hout
        have hFM : Block.Preceq sigma.F M.erase :=
          NamedFinalizationBridge.finalized_preceq_of_height_lt
            S rho M B hsb core.toNamedRootCollisionFree
              (hfacts.1 M hMheld) hBscope hheight
        refine ⟨M.erase, ?_, hFM, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_of_mem hMraw
        · rw [hUsigma]
          change max U.h_max sigma.h - 1 ≤
            (if M.erase = B.erase then
              Protocol.named_transition S.E S.cfg
                (before.core.σ B.erase.parent) B
            else before.core.σ M.erase).h
          rw [if_neg hMne, hco.2.2.2.2 M hMheld, hMheight, ← hUmax,
            hmaxEq]
          exact Nat.sub_le _ _
    have hviableAfter : sigma.F ∈
        Protocol.viable_tree afterJ.σ afterJ.F
          afterJ.h_max afterJ.T := by
      dsimp only [afterJ, afterMax]
      split_ifs <;> exact hviable
    rw [hpostEq, hderived.1]
    change Block.Preceq sigma.F (Protocol.update_finality U sigma).F
    by_cases halready : Block.Preceq sigma.F U.F
    · exact Block.preceq_trans halready
        (update_finality_F U sigma)
    · change Block.Preceq sigma.F
          (if Block.prec afterJ.F sigma.F &&
              Block.preceq sigma.F afterJ.J &&
              decide (sigma.F ∈ Protocol.viable_tree afterJ.σ
                afterJ.F afterJ.h_max afterJ.T) then
            ({ afterJ with F := sigma.F } : Protocol.Store V)
          else afterJ).F
      exact absorb_finality_step U afterJ sigma (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) halready hviable hafterJ

private theorem runBlock_unique_of_erase_eq
    {S : Setup V} {rho : NamedRun V}
    (roots : NamedRootCollisionFree S rho)
    {A B : NamedBlock V} (hA : NamedRun.blockInRun S rho A)
    (hB : NamedRun.blockInRun S rho B) (herase : A.erase = B.erase) :
    A = B :=
  roots.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A))
    (Or.inr (Proofs.NamedAncestry.named_self B)) (by
      rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

private theorem held_find_at_strict
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {reader : V} (hreader : reader ∈ rho.honest) (time : Time)
    (B : NamedBlock V)
    (hB : B ∈ (NamedRun.stateBeforeTime S rho time reader).st.bodies) :
    Block.find?
      (NamedRun.stateBeforeTime S rho time reader).st.core.T B.root =
        some B.erase := by
  have hco :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time reader).1.1.1
  have hBraw : B.erase ∈
      (NamedRun.stateBeforeTime S rho time reader).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho core.sorted time
  have hBprefix : B ∈ (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hB
  have hBscope : NamedRun.blockInRun S rho B :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hBprefix
  rw [← Proofs.NamedWire.erase_root B]
  apply Proofs.Optimistic.find?_eq_some_of_unique hBraw
  intro X hX hroot
  obtain ⟨C, hCheld, hCErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho time reader hX
  have hCprefix : C ∈ (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hCheld
  have hCscope : NamedRun.blockInRun S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hCprefix
  have hCB : C = B := core.toNamedRootCollisionFree.root_injective
    C B hCscope hBscope C B
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self B)) (by
        rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root B,
          hCErase, hroot])
  rw [← hCErase, hCB]

private theorem accepted_carrier_finality_preceq
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hsb : SlashableBound S rho) {target : V}
    (htarget : target ∈ rho.honest) {i : Nat} {B : NamedBlock V}
    {t : Time} (hBscope : NamedRun.blockInRun S rho B)
    (hacc : NamedRun.acceptsAt S rho i target (.block B) t)
    (hfloor : Block.Preceq
      (NamedRun.stateBefore S rho i target).st.core.F
      (Protocol.derive_named S.E S.cfg B).F) :
    Block.Preceq (Protocol.derive_named S.E S.cfg B).F
      (NamedRun.stateBefore S rho (i + 1) target).st.core.F := by
  obtain ⟨before, hcall, hnew, hpost, hbridge⟩ :=
    NamedOutageHistory.HeldSkipProducers.accepted_block_fresh_call
      S rho i target B t hacc
  exact Block.preceq_trans
    (fresh_receipt_absorbs_finality S rho core hsb htarget B hBscope
      before hcall hnew hpost hfloor) hbridge

/-- One post-GST relay delay orders an earlier honest finalized root below a
later honest finalized root. The proof relays the exact named finalization
carrier. Whole-run finality agreement supplies the receiver guard in the only
branch where delivery is needed. -/
theorem finalized_preceq_of_evidence_delivered
    (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {source target : V}
    (hsource : source ∈ rho.honest) (htarget : target ∈ rho.honest)
    {read out : Time} (hpost : S.E.t_GST ≤ read)
    (hhop : read + S.E.Δ = out) (hhor : out ≤ rho.horizon) :
    Block.Preceq
      (NamedRun.stateBeforeTime S rho read source).st.core.F
      (NamedRun.stateBeforeTime S rho out target).st.core.F := by
  let core := adm.toNamedAdmissibleCore
  have hsafe := NamedFinalityAgreement.stateBeforeTime_finalized_compatible
    S rho core.toNamedScheduleWellFormed hsb core.toNamedRootCollisionFree
      read out source target hsource htarget
  simp only [Block.compatible, Bool.or_eq_true] at hsafe
  rcases hsafe with hforward | hreverse
  · exact hforward
  · obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho core.sorted read
    obtain ⟨D, hDread, hDF, -⟩ :=
      NamedFinalizationBridge.finalization_carrier_stateBeforeTime
        S rho read source
    have hDprefix : D ∈
        (NamedRun.stateBefore S rho n source).st.bodies := by
      rw [← hn]
      exact hDread
    have hDscope : NamedRun.blockInRun S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hDprefix
    rcases NamedOutageProvenance.held_block_origin
        S rho n source hDprefix with hgen | ⟨j, hj, t, hacc⟩
    · subst D
      rw [← hDF]
      change Block.Preceq Block.genesis _
      exact Protocol.preceq_genesis _
    · obtain ⟨e, he, -, het⟩ := hacc.1.2
      have htRead : t < read := by
        simpa only [het] using hbefore j e hj he
      have hDpos : 0 < D.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt
          (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
          S rho target D out := by
        intro k hk
        have hmono := stateBefore_F_preceq_stateBeforeTime_of_prefix
          S rho core.sorted (w := target) hk
        exact Block.preceq_trans hmono
          (Block.preceq_trans hreverse (by
            rw [← hDF]
            exact
              (NamedDerivationGeometry.derive_named_anchors_preceq
                S.E S.cfg D).1))
      have hadmit :=
        Protocol.block_admittedBefore_of_accepted_after_cutoff
          S adm hsource htarget hDpos hacc htRead hpost hhop hhor hFhist
      obtain ⟨C, hCErase, k, tk, hCacc, htk⟩ := hadmit
      have hCmem : C ∈
          (NamedRun.stateBefore S rho (k + 1) target).st.bodies := by
        simpa only [NamedReceipt.processed, decide_eq_true_eq] using hCacc.2.2
      have hCscope : NamedRun.blockInRun S rho C :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hCmem
      have hCD : C = D := runBlock_unique_of_erase_eq
        core.toNamedRootCollisionFree hCscope hDscope hCErase
      subst C
      have hkOut : k < strictEventIndex rho out := by
        obtain ⟨event, hevent, -, heventTime⟩ := hCacc.1.2
        by_contra hnot
        have houtLe : out ≤ event.time :=
          Proofs.Optimistic.le_time_of_index_ge S core.toNamedScheduleWellFormed
            (Nat.le_of_not_gt hnot) hevent
        exact (not_le_of_gt htk) (by simpa only [heventTime] using houtLe)
      have hmonoBefore := Protocol.stateBefore_F_mono
        S rho target (Nat.le_of_lt hkOut)
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S core.toNamedScheduleWellFormed target out] at hmonoBefore
      have hfloor : Block.Preceq
          (NamedRun.stateBefore S rho k target).st.core.F
          (Protocol.derive_named S.E S.cfg D).F :=
        Block.preceq_trans hmonoBefore (by
          rw [hDF]
          exact hreverse)
      have habsorb := accepted_carrier_finality_preceq
        S rho core hsb htarget hDscope hCacc hfloor
      have hmonoAfter := Protocol.stateBefore_F_mono
        S rho target (Nat.succ_le_of_lt hkOut)
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S core.toNamedScheduleWellFormed target out] at hmonoAfter
      rw [← hDF]
      exact Block.preceq_trans habsorb hmonoAfter

#print axioms finalized_preceq_of_evidence_delivered

/-- Core synchrony supplies both cutoff facts once GST is no later than the
early G2 cutoff. -/
theorem twoCutoffDelivery_of_core
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hgst : S.E.t_GST ≤ early S.E S.hc r .g2) :
    TwoCutoffDelivery S rho r where
  earlyAttest := by
    intro source hsource i a t hacc ht target htarget hmissing hhor
    have hmax : max t S.E.t_GST ≤ early S.E S.hc r .g2 :=
      max_le ht.le hgst
    have hdeadline : max t S.E.t_GST + S.E.Δ ≤
        early S.E S.hc r .g1 := by
      rw [← early_g2_add_delta_eq_g1 S r]
      exact Int.add_le_add_right hmax S.E.Δ
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      core.toNamedSynchrony.relay_attest source hsource i a t hacc
        target htarget hmissing (hdeadline.trans hhor) rfl
    exact ⟨t', hlo, hhi.trans_le hdeadline, j, hcall⟩
  lateAttest := by
    intro source hsource i a t hacc ht target htarget hmissing hhor
    have hgstLate : S.E.t_GST ≤ late S.E S.hc r .g1 := by
      exact hgst.trans (by
        simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
        linarith [S.E.Δ_pos])
    have hmax : max t S.E.t_GST ≤ late S.E S.hc r .g1 :=
      max_le ht.le hgstLate
    have hdeadline : max t S.E.t_GST + S.E.Δ ≤
        late S.E S.hc r .g2 := by
      rw [← late_g1_add_delta_eq_g2 S r]
      exact Int.add_le_add_right hmax S.E.Δ
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      core.toNamedSynchrony.relay_attest source hsource i a t hacc
        target htarget hmissing (hdeadline.trans hhor) rfl
    exact ⟨t', hlo, hhi.trans_le hdeadline, j, hcall⟩

/-- Core synchrony supplies the G1-to-G0 cutoff facts. -/
theorem g1G0TwoCutoffDelivery_of_core
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hgst : S.E.t_GST ≤ early S.E S.hc r .g1) :
    G1G0TwoCutoffDelivery S rho r where
  earlyAttest := by
    intro source hsource i a t hacc ht target htarget hmissing hhor
    have hmax : max t S.E.t_GST ≤ early S.E S.hc r .g1 :=
      max_le ht.le hgst
    have hdeadline : max t S.E.t_GST + S.E.Δ ≤
        early S.E S.hc r .g0 := by
      rw [← early_g1_add_delta_eq_g0 S r]
      exact Int.add_le_add_right hmax S.E.Δ
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      core.toNamedSynchrony.relay_attest source hsource i a t hacc
        target htarget hmissing (hdeadline.trans hhor) rfl
    exact ⟨t', hlo, hhi.trans_le hdeadline, j, hcall⟩
  lateAttest := by
    intro source hsource i a t hacc ht target htarget hmissing hhor
    have hgstLate : S.E.t_GST ≤ late S.E S.hc r .g0 := by
      exact hgst.trans (by
        simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
        linarith [S.E.Δ_pos])
    have hmax : max t S.E.t_GST ≤ late S.E S.hc r .g0 :=
      max_le ht.le hgstLate
    have hdeadline : max t S.E.t_GST + S.E.Δ ≤
        late S.E S.hc r .g1 := by
      rw [← late_g0_add_delta_eq_g1 S r]
      exact Int.add_le_add_right hmax S.E.Δ
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      core.toNamedSynchrony.relay_attest source hsource i a t hacc
        target htarget hmissing (hdeadline.trans hhor) rfl
    exact ⟨t', hlo, hhi.trans_le hdeadline, j, hcall⟩


/-- The only semantic guard needed by the cross-reader relay. The network
transport moves the signed row. These two fields state that the row's named
body passes the destination reader's finalized-prefix test. -/
structure CrossReaderBodyReadyGuard
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender u,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) sender →
    localCovers
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      u.confirmed B = true →
    DecoupledConsensusModel.Protocol.bodyReady
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 target).st.core.F
      (early S.E S.hc r .g1) u = true
  backward : ∀ sender u,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g1) sender →
    DecoupledConsensusModel.Protocol.bodyReady
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 source).st.core.F
      (late S.E S.hc r .g2) u = true

/-- The cap facts needed for the two body-open checks. They mention
only the heads that occur in the source and target interpreted inputs. -/
structure CrossReaderFinalizedBelow
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender u root H,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) sender →
    localCovers
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      u.confirmed B = true →
    u.confirmed = some root →
    Block.find?
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView.T root =
        some H →
    Block.Preceq (phaseRead S rho r .g1 target).st.core.F H
  backward : ∀ sender u root H,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g1) sender →
    u.confirmed = some root →
    Block.find?
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView.T root =
        some H →
    Block.compatible H (phaseRead S rho r .g2 source).st.core.F = true

/-- Finality safety and one-delay evidence relay supply the reverse reader
guard. The forward guard is the selected-block cap from the consumer. -/
theorem crossReaderFinalizedBelow_of_finalitySafety_and_relay
    (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round}
    (hgst : S.E.t_GST ≤ early S.E S.hc r .g2)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
        (phaseRead S rho r .g2 source).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) sender →
      localCovers
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
        u.confirmed B = true →
      u.confirmed = some root →
      Block.find?
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView.T root =
          some H →
      Block.Preceq (phaseRead S rho r .g1 target).st.core.F H) :
    CrossReaderFinalizedBelow S rho r source target B := by
  have hgstDomain : S.E.t_GST ≤ domain S.E S.hc r .g2 :=
    hgst.trans (early_g2_le_domain_g2 S r)
  have hg1Horizon : domain S.E S.hc r .g1 ≤ rho.horizon :=
    (domain_g1_le_domain_g0 S r).trans horizon
  have hForder := finalized_preceq_of_evidence_delivered
    S adm hsb hsource htarget hgstDomain
      (domain_g2_add_delta_eq_g1 S r) hg1Horizon
  refine ⟨hforward, ?_⟩
  intro sender u root H hu hconf hfind
  obtain ⟨-, hready⟩ := Finset.mem_filter.mp hu
  simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf, hfind,
    Bool.and_eq_true] at hready
  have hcompat := hready.2
  simp only [Block.compatible, Bool.or_eq_true] at hcompat ⊢
  rcases hcompat with hHF | hFH
  · rcases Block.preceq_linear hForder hHF with hsourceH | hHsource
    · exact Or.inr hsourceH
    · exact Or.inl hHsource
  · exact Or.inr (Block.preceq_trans hForder hFH)

#print axioms crossReaderFinalizedBelow_of_finalitySafety_and_relay

/-- Transport the referenced named bodies at the two fixed cutoffs, then use
the caller's finality cap to discharge `bodyReady` at the other reader. -/
theorem crossReaderBodyReadyGuard_of_finalizedBelow
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r)
    (hgst : S.E.t_GST ≤ early S.E S.hc r .g2)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hbelow : CrossReaderFinalizedBelow S rho r source target B) :
    CrossReaderBodyReadyGuard S rho r source target B := by
  have hearlyHorizon : early S.E S.hc r .g1 ≤ rho.horizon :=
    (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  have hlateHorizon : late S.E S.hc r .g2 ≤ rho.horizon := by
    rw [late_g2_eq_domain_g2]
    exact (NamedOutageHistory.GuardedHelpers.domain_g2_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  refine ⟨?_, ?_⟩
  · intro sender u hu hcover
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (phaseRead S rho r .g2 source).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈ (phaseRead S rho r .g2 source).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g2) source).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHearly : Hn ∈ (NamedRun.stateBeforeTime S rho
            (early S.E S.hc r .g2) source).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (NamedOutageHistory.GuardedHelpers.early_g2_public S r hr)
            hHbody
          simpa only [hHnErase] using hstamp
        have hdeadline : max (early S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
            early S.E S.hc r .g1 := by
          rw [max_eq_left hgst, early_g2_add_delta_eq_g1]
        have hFH : Block.Preceq
            (phaseRead S rho r .g1 target).st.core.F Hn.erase := by
          rw [hHnErase]
          exact hbelow.forward sender u root H hu hcover hconf hfind
        obtain ⟨-, hstampTarget, hfindTarget⟩ :=
          NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
            S rho core source hsource target htarget Hn
            (early S.E S.hc r .g2) (early S.E S.hc r .g1)
            (domain S.E S.hc r .g1) hHearly hdeadline
            (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r)
            hearlyHorizon hFH
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindTarget' : Block.find?
            (phaseRead S rho r .g1 target).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [phaseRead, Proofs.NamedWire.erase_root] using hfindTarget
        change (match Block.find?
          (phaseRead S rho r .g1 target).st.core.T root with
          | none => false
          | some head => stampedBefore
              (phaseRead S rho r .g1 target).st.core.timestamp_block
              (early S.E S.hc r .g1) head &&
            Block.compatible head
              (phaseRead S rho r .g1 target).st.core.F) = true
        rw [← hroot, hfindTarget', Bool.and_eq_true]
        refine ⟨hstampTarget, ?_⟩
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hFH
  · intro sender u hu
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (phaseRead S rho r .g1 target).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈ (phaseRead S rho r .g1 target).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g1) target).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHlate : Hn ∈ (NamedRun.stateBeforeTime S rho
            (late S.E S.hc r .g1) target).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (NamedOutageClosure.q10_late_g1_public S r hr) hHbody
          simpa only [hHnErase] using hstamp
        have hgstLate : S.E.t_GST ≤ late S.E S.hc r .g1 := by
          exact hgst.trans (by
            simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
            linarith [S.E.Δ_pos])
        have hdeadline : max (late S.E S.hc r .g1) S.E.t_GST + S.E.Δ ≤
            late S.E S.hc r .g2 := by
          rw [max_eq_left hgstLate, late_g1_add_delta_eq_g2]
        have hcompatSource : Block.compatible Hn.erase
            (phaseRead S rho r .g2 source).st.core.F = true := by
          rw [hHnErase]
          exact hbelow.backward sender u root H hu hconf hfind
        obtain ⟨hHsource, hstampSource, hfindSource⟩ :
            Hn ∈ (phaseRead S rho r .g2 source).st.bodies ∧
            stampedBefore
              (phaseRead S rho r .g2 source).st.core.timestamp_block
              (late S.E S.hc r .g2) Hn.erase = true ∧
            Block.find? (phaseRead S rho r .g2 source).st.core.T
              Hn.root = some Hn.erase := by
          simp only [Block.compatible, Bool.or_eq_true] at hcompatSource
          rcases hcompatSource with hHF | hFH
          · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime
              S rho (domain S.E S.hc r .g2) source
            have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
              S rho (domain S.E S.hc r .g2) source
            have hHraw : Hn.erase ∈
                (phaseRead S rho r .g2 source).st.core.T :=
              Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
                Hn.erase _ hFmem hHF
            obtain ⟨K, hKheld, hKErase⟩ :=
              Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
                S rho (domain S.E S.hc r .g2) source hHraw
            obtain ⟨ns, hns, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
              S rho core.sorted (domain S.E S.hc r .g2)
            have hKprefix : K ∈
                (NamedRun.stateBefore S rho ns source).st.bodies := by
              rw [← hns]
              exact hKheld
            have hKscope : NamedRun.blockInRun S rho K :=
              Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hKprefix
            obtain ⟨nt, hnt, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
              S rho core.sorted (domain S.E S.hc r .g1)
            have hHprefix : Hn ∈
                (NamedRun.stateBefore S rho nt target).st.bodies := by
              rw [← hnt]
              exact hHbody
            have hHscope : NamedRun.blockInRun S rho Hn :=
              Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hHprefix
            have hKH : K = Hn := runBlock_unique_of_erase_eq
              core.toNamedRootCollisionFree hKscope hHscope
                hKErase
            subst K
            have hstamp :=
              NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
                S rho core.toNamedScheduleWellFormed source
                  (domain S.E S.hc r .g2) Hn hKheld
            refine ⟨hKheld, ?_, ?_⟩
            · simpa only [phaseRead, late_g2_eq_domain_g2] using hstamp
            · exact held_find_at_strict S rho core hsource
                (domain S.E S.hc r .g2) Hn hKheld
          · simpa only [phaseRead, Proofs.NamedWire.erase_root] using
              (NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
                S rho core target htarget source hsource Hn
                (late S.E S.hc r .g1) (late S.E S.hc r .g2)
                (domain S.E S.hc r .g2) hHlate hdeadline
                (late_g2_eq_domain_g2 S r).le hlateHorizon hFH)
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindSource' : Block.find?
            (phaseRead S rho r .g2 source).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [phaseRead, Proofs.NamedWire.erase_root] using hfindSource
        change (match Block.find?
          (phaseRead S rho r .g2 source).st.core.T root with
          | none => false
          | some head => stampedBefore
              (phaseRead S rho r .g2 source).st.core.timestamp_block
              (late S.E S.hc r .g2) head &&
            Block.compatible head
              (phaseRead S rho r .g2 source).st.core.F) = true
        rw [← hroot, hfindSource', Bool.and_eq_true]
        refine ⟨hstampSource, ?_⟩
        exact hcompatSource

#print axioms crossReaderBodyReadyGuard_of_finalizedBelow

private theorem relative_gradeBool_zero_namedFrame
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem relative_freezeRoot_zero_namedFrame
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) :
    DecoupledConsensusModel.Protocol.freezeRoot E gv F eta 0 early late = none := by
  unfold DecoupledConsensusModel.Protocol.freezeRoot
  have hempty : gv.T.filter (fun B =>
      DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = true) = ∅ := by
    ext B
    simp [relative_gradeBool_zero_namedFrame E gv F eta early late B]
  rw [hempty]
  exact deepest?_empty

/-- A named height-regime frame supplies the cross-reader body guard needed
by the prepared first-interior G1 transport. The forward cap relays the
target reader's G1-domain finalization to the source reader's G0-domain read,
then uses finality monotonicity up to the action read and the selected Q2's
filtered-tree membership. -/
theorem crossReaderBodyReadyGuard_of_namedHeightRegimeFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    {stop : Nat} {H : Height} {Prev : NamedBlock V}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (_hframe : NamedHeightRegimeFrame S rho H
      (stop - 1) Prev a.round)
    (hiStart : inclusiveEventIndex rho (S.a r0) ≤ i)
    (_hiStop : i < stop) (haHon : a.val_index ∈ rho.honest)
    (hiEvent : rho.events[i]? = some (Event.tick a.val_index ta))
    (hiOutput : Object.attest a ∈
      NamedRun.emittedAt S rho i a.val_index ta)
    (_hrow : a.height_pair.erase.height? = some (H + 1))
    (_hfrontier : honestHMaxBeforeIndex S rho i < H + 2) :
    ∀ w, w ∈ rho.honest → ∀ Q,
      PhaseGrades.nodeQ2 S
        (actionReadAt S rho a.val_index a.round) a.round = some Q →
      CrossReaderBodyReadyGuard S rho a.round a.val_index w Q := by
  have hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta :=
    ⟨i, hiEvent, hiOutput⟩
  have htime : ta = S.a a.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hactionHorizon : S.a a.round ≤ rho.horizon := by
    have hin :=
      (adm.in_horizon (Event.tick a.val_index ta)
        (List.mem_of_getElem? hiEvent)).2
    simpa only [Event.time, htime] using hin
  have hroundFromStart : r0 ≤ a.round := by
    by_contra hnot
    have haRoundLt : a.round < r0 := Nat.lt_of_not_ge hnot
    have htimeLt : ta < S.a r0 := by
      rw [htime]
      exact action_strictMono S haRoundLt
    have hstartCursor : strictEventIndex rho (S.a r0) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho (S.a r0)).trans hiStart
    have htimeLe : S.a r0 ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        hstartCursor hiEvent
    exact (not_le_of_gt htimeLt) htimeLe
  have ready : GradeRoundReady S rho a.round :=
    gradeRoundReady_of_action_horizon
      S hgst hroundFromStart hactionHorizon
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  intro w hw Q hQ
  have hr : 0 < a.round := by
    apply Nat.pos_of_ne_zero
    intro hzero
    let actionIndex := strictEventIndex rho (S.a a.round)
    have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (S.a a.round)
    have hreadp := congrFun hread a.val_index
    have hselected := hQ
    simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hselected
    unfold actionReadAt NamedActionReads.actionReadAt at hselected
    rw [hreadp] at hselected
    have hselected' : Protocol.grade2_block_with
        (NamedProfile.gradeContract
          (NamedActionReads.actionReadFrom S
            (NamedRun.stateBefore S rho actionIndex a.val_index)
            a.round).cache)
        S.E S.hc
        (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho actionIndex a.val_index)
          a.round).st.core.toHealing a.round = some Q := by
      simpa only [actionIndex] using hselected
    obtain ⟨j, raw, -, -, hfreeze, -⟩ :=
      contractQ2_capture_at_action_index
        S rho actionIndex a.val_index a.round hselected'
    rw [hzero, relative_freezeRoot_zero_namedFrame] at hfreeze
    cases hfreeze
  have hdomainAction :
      domain S.E S.hc a.round .g0 ≤ S.a a.round :=
    FrameForward.domain_le_a S a.round .g0
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc a.round .g0) a.val_index).st.core.F
      (NamedRun.stateBeforeTime S rho
        (S.a a.round) a.val_index).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted
        (domain S.E S.hc a.round .g0),
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted (S.a a.round)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho a.val_index
      (NamedOutageClosure.strict_lengths_mono rho hdomainAction)
  have hFQAction : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (S.a a.round) a.val_index).st.core.F Q := by
    have hactive := actionQ2_mem_filteredTree S rho a.val_index a.round hQ
    have hFQ := NamedOutageClosure.q10_filtered_F hactive
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hFQ
  have hsourceFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc a.round .g0) a.val_index).st.core.F Q :=
    Block.preceq_trans hmono hFQAction
  have hforward : ∀ sender u root Head,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (phaseRead S rho a.round .g2 a.val_index).st.core.toHealing.gradeView
        (phaseRead S rho a.round .g2 a.val_index).st.core.F
        S.hc.η_SG a.round (early S.E S.hc a.round .g2) sender →
      localCovers
        (phaseRead S rho a.round .g2 a.val_index).st.core.toHealing.gradeView
        u.confirmed Q = true →
      u.confirmed = some root →
      Block.find?
        (phaseRead S rho a.round .g2 a.val_index).st.core.toHealing.gradeView.T
        root = some Head →
      Block.Preceq
        (phaseRead S rho a.round .g1 w).st.core.F Head := by
    intro sender u root Head _ hcover hconf hfind
    have hpost : S.E.t_GST ≤ domain S.E S.hc a.round .g1 :=
      ready.1.trans (by
        simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
        linarith [S.E.Δ_pos])
    have hhop : domain S.E S.hc a.round .g1 + S.E.Δ =
        domain S.E S.hc a.round .g0 := by
      simp only [domain, Phase.domainOffset]
      ring
    have hrelay : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc a.round .g1) w).st.core.F
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc a.round .g0) a.val_index).st.core.F :=
      finalized_preceq_of_evidence_delivered
        S adm hsb hw haHon hpost hhop ready.2
    have hQHead : Block.Preceq Q Head := by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      change Block.find?
        (phaseRead S rho a.round .g2 a.val_index).st.core.T root = some Head
        at hfind
      rw [hfind] at hcover
      exact hcover
    exact Block.preceq_trans hrelay
      (Block.preceq_trans hsourceFQ hQHead)
  have hfinalized :=
    crossReaderFinalizedBelow_of_finalitySafety_and_relay
      S adm hsb ready.1 ready.2 haHon hw hforward
  exact crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 haHon hw hfinalized

#print axioms crossReaderBodyReadyGuard_of_namedHeightRegimeFrame

private structure CrossReaderTokenTransport
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender x,
    x ∈ readyView
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) sender →
    localCovers
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      x.key B = true →
    x ∈ readyView
        (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
        (phaseRead S rho r .g1 target).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g1) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g1) sender) x.round
  lateBack : ∀ sender x,
    x ∈ readyView
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g1) sender →
    x ∈ readyView
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
        (phaseRead S rho r .g2 source).st.core.F
        S.hc.η_SG r (late S.E S.hc r .g2) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g2) sender) x.round
  rawBack : ∀ sender x,
    x ∈ rawView
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      S.hc.η_SG r (late S.E S.hc r .g1) sender →
    x ∈ rawView
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
        S.hc.η_SG r (late S.E S.hc r .g2) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g2) sender) x.round

private theorem crossReaderTokenTransport_of_delivery
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (source target : V) (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) (B : Block V)
    (guard : CrossReaderBodyReadyGuard S rho r source target B) :
    CrossReaderTokenTransport S rho r source target B := by
  have hearlyHorizon : early S.E S.hc r .g1 ≤ rho.horizon :=
    (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  have hlateHorizon : late S.E S.hc r .g2 ≤ rho.horizon := by
    rw [late_g2_eq_domain_g2]
    exact (NamedOutageHistory.GuardedHelpers.domain_g2_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  refine ⟨?_, ?_, ?_⟩
  · intro sender x hx hcover
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hraw, -⟩ := Finset.mem_filter.mp hu
    have hval : u.val_index = sender := (Finset.mem_filter.mp hraw).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g2_raw_input_source_acceptance S rho
        core.toNamedScheduleWellFormed source r sender u hraw
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hrelay := NamedRawRelay.accepted_sg_vote_or_equiv_at_g1_of_relay
      S rho r core hacc hbefore hwindow (fun reader hreader hmissing =>
        delivery.earlyAttest source hsource i a accepted hacc hbefore
          reader hreader hmissing hearlyHorizon) target htarget
    simp only [hproj, hidx] at hrelay
    rcases hrelay with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (Finset.mem_filter.mpr ⟨hexact, guard.forward sender u hu hcover⟩))
    · have hmono := GradeCutoffMono.rawView_mono
        (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
        S.hc.η_SG r
        (NamedOutageHistory.GuardedHelpers.early_g1_le_late_g1 S r)
        sender
      exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        hmono (Finset.mem_image_of_mem _ hleft),
        DecoupledConsensusModel.Protocol.token right,
        hmono (Finset.mem_image_of_mem _ hright), hlr.trans hround,
        hrr.trans hround, hne⟩
  · intro sender x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hraw, -⟩ := Finset.mem_filter.mp hu
    have hval : u.val_index = sender := (Finset.mem_filter.mp hraw).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g1_late_raw_input_acceptance
        S rho core.toNamedScheduleWellFormed target r sender u hraw
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hone :=
      NamedHealthyLateRelay.accepted_sg_vote_or_equiv_at_g2_late_of_relay
        S rho r core hacc hbefore hwindow
        (fun reader hreader hmissing =>
          delivery.lateAttest target htarget i a accepted hacc hbefore
            reader hreader hmissing hlateHorizon) source hsource
    simp only [hproj, hidx] at hone
    rcases hone with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (Finset.mem_filter.mpr ⟨hexact, guard.backward sender u hu⟩))
    · exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        Finset.mem_image_of_mem _ hleft, DecoupledConsensusModel.Protocol.token right,
        Finset.mem_image_of_mem _ hright, hlr.trans hround,
        hrr.trans hround, hne⟩
  · intro sender x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hval : u.val_index = sender := (Finset.mem_filter.mp hu).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g1_late_raw_input_acceptance
        S rho core.toNamedScheduleWellFormed target r sender u hu
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hone :=
      NamedHealthyLateRelay.accepted_sg_vote_or_equiv_at_g2_late_of_relay
        S rho r core hacc hbefore hwindow
        (fun reader hreader hmissing =>
          delivery.lateAttest target htarget i a accepted hacc hbefore
            reader hreader hmissing hlateHorizon) source hsource
    simp only [hproj, hidx] at hone
    rcases hone with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem _ hexact)
    · exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        Finset.mem_image_of_mem _ hleft, DecoupledConsensusModel.Protocol.token right,
        Finset.mem_image_of_mem _ hright, hlr.trans hround,
        hrr.trans hround, hne⟩

private theorem localCovers_iff_of_cross_late_ready
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (r : Round) (source target : V) (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) (sender : V) (B : Block V)
    (x : Token (Option BlockId))
    (hsourceReady : x ∈ readyView
      (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 source).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g2) sender)
    (htargetReady : x ∈ readyView
      (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g1) sender) :
    (localCovers
        (phaseRead S rho r .g2 source).st.core.toHealing.gradeView
        x.key B = true ↔
      localCovers
        (phaseRead S rho r .g1 target).st.core.toHealing.gradeView
        x.key B = true) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hsourceReady
  obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp htargetReady
  have hkey : z.confirmed = u.confirmed :=
    congrArg Token.key hzu
  obtain ⟨_, hbodyU⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hbodyZ⟩ := Finset.mem_filter.mp hz
  cases hconf : u.confirmed with
  | none =>
      have hconfZ : z.confirmed = none := hkey.trans hconf
      simp [DecoupledConsensusModel.Protocol.token, localCovers, Protocol.head_covers,
        hconf, hconfZ]
  | some root =>
      have hconfZ : z.confirmed = some root := hkey.trans hconf
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hbodyU
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconfZ] at hbodyZ
      cases hfindU : Block.find?
          (phaseRead S rho r .g2 source).st.core.toHealing.gradeView.T root with
      | none => rw [hfindU] at hbodyU; exact absurd hbodyU (by simp)
      | some H =>
          cases hfindZ : Block.find?
              (phaseRead S rho r .g1 target).st.core.toHealing.gradeView.T root with
          | none => rw [hfindZ] at hbodyZ; exact absurd hbodyZ (by simp)
          | some K =>
              have hHK :=
                NamedOutageHistory.GuardedHelpers.find_agree S rho core
                  source target hsource htarget
                  (domain S.E S.hc r .g2) (domain S.E S.hc r .g1)
                  root hfindU hfindZ
              subst K
              simp [DecoupledConsensusModel.Protocol.token, localCovers,
                Protocol.head_covers, hconf, hconfZ, hfindU, hfindZ]

private theorem clean_excludes_equivocation
    {Key : Type} {raw : Finset (Token Key)} {k j : Nat}
    (hclean : CleanFrom raw k) (hkj : k ≤ j) :
    ¬ EquivocationAt raw j := by
  rintro ⟨x, hx, y, hy, hxj, hyj, hne⟩
  apply hne
  exact hclean x hx y hy (by simpa only [hxj] using hkj)
    (hxj.trans hyj.symm)

private theorem equivocation_opposes_of_round_bound
    {Key Blk : Type} (covers : Key → Blk → Prop)
    {early late raw : Finset (Token Key)} {B : Blk} {k : Nat}
    (hbound : ∀ u ∈ early, u.round ≤ k)
    (heq : EquivocationAt raw k) :
    Opposes covers early late raw B := by
  obtain ⟨x, hx, y, hy, hxk, hyk, hne⟩ := heq
  exact Or.inr ⟨x, hx, y, hy,
    fun u hu => by simpa only [hxk] using hbound u hu,
    hxk.trans hyk.symm, hne⟩

/-- A validator that supports `B` at an honest G2 reader still supports it at
an honest G1 reader. The delivery may expose an equivocation instead of the
exact row; source cleanliness rules out that branch. -/
theorem positive_g2_at_v_imp_positive_g1_at_w
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B : Block V) (guard : CrossReaderBodyReadyGuard S rho r v w B)
    (sender : V)
    (hpositive : positive
      (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2)
      sender B = true) :
    positive
      (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1)
      sender B = true := by
  let srcEarly := readyView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g2) sender
  let srcLate := readyView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g2) sender
  let srcRaw := rawView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g2) sender
  let dstEarly := readyView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) sender
  let dstLate := readyView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g1) sender
  let dstRaw := rawView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g1) sender
  let srcCovers := fun key block => localCovers
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView key block = true
  let dstCovers := fun key block => localCovers
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView key block = true
  have hsrc : Supports srcCovers srcEarly srcLate srcRaw B := by
    simpa only [srcEarly, srcLate, srcRaw, srcCovers, positive,
      decide_eq_true_eq] using hpositive
  have hSL : srcEarly ⊆ srcLate := by
    exact GradeCutoffMono.readyView_mono _ _ _ _
      (NamedOutageHistory.GuardedHelpers.early_g2_le_late_g2 S r) sender
  have hSR : srcLate ⊆ srcRaw :=
    GradeCutoffMono.readyView_subset_rawView _ _ _ _ _ sender
  have hDL : dstEarly ⊆ dstLate := by
    exact GradeCutoffMono.readyView_mono _ _ _ _
      (NamedOutageHistory.GuardedHelpers.early_g1_le_late_g1 S r) sender
  let tr := crossReaderTokenTransport_of_delivery
    S rho core r delivery horizon v w hv hw B guard
  have hEqBack : ∀ k, EquivocationAt dstRaw k →
      EquivocationAt srcRaw k := by
    intro k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (tr.rawBack sender) hk
  obtain ⟨u, hu, hmax, hcover, hclean, hsweep⟩ := hsrc
  have huDst : u ∈ dstEarly := by
    rcases tr.forward sender u hu hcover with h | h
    · exact h
    · exact False.elim
        (clean_excludes_equivocation hclean le_rfl (hEqBack _ h))
  obtain ⟨x, hx, hmaxDst⟩ :=
    dstEarly.exists_max_image Token.round ⟨u, huDst⟩
  have hux : u.round ≤ x.round := hmaxDst u huDst
  have hxSrc : x ∈ srcLate := by
    rcases tr.lateBack sender x (hDL hx) with h | h
    · exact h
    · exact False.elim (clean_excludes_equivocation hclean hux h)
  have hxCoverSrc : srcCovers x.key B := by
    by_cases heq : u.round = x.round
    · have hkey := hclean u (hSR (hSL hu)) x (hSR hxSrc)
        le_rfl heq
      simpa only [← hkey] using hcover
    · exact hsweep x hxSrc (Nat.lt_of_le_of_ne hux heq)
  have hxCoverDst : dstCovers x.key B := by
    exact (localCovers_iff_of_cross_late_ready S rho core r v w hv hw
      sender B x hxSrc (hDL hx)).mp hxCoverSrc
  simp only [positive, decide_eq_true_eq]
  change Supports dstCovers dstEarly dstLate dstRaw B
  refine ⟨x, hx, hmaxDst, hxCoverDst, ?_, ?_⟩
  · intro y hy z hz hxy hyz
    by_contra hne
    exact clean_excludes_equivocation hclean (hux.trans hxy)
      (hEqBack _ ⟨y, hy, z, hz, rfl, hyz.symm, hne⟩)
  · intro y hy hxy
    rcases tr.lateBack sender y hy with hySrc | hyEq
    · have hyCoverSrc := hsweep y hySrc (lt_of_le_of_lt hux hxy)
      exact (localCovers_iff_of_cross_late_ready S rho core r v w hv hw
        sender B y hySrc hy).mp hyCoverSrc
    · exact False.elim
        (clean_excludes_equivocation hclean (hux.trans hxy.le) hyEq)

/-- A validator that opposes `B` at the G1 reader already opposes it at the
G2 reader. A returned equivocation pair is itself an opposition witness. -/
theorem opposing_g1_at_w_imp_opposing_g2_at_v
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B : Block V) (guard : CrossReaderBodyReadyGuard S rho r v w B)
    (sender : V)
    (hopposing : opposing
      (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1)
      sender B = true) :
    opposing
      (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2)
      sender B = true := by
  let srcEarly := readyView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g2) sender
  let srcLate := readyView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g2) sender
  let srcRaw := rawView
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g2) sender
  let dstEarly := readyView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) sender
  let dstLate := readyView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g1) sender
  let dstRaw := rawView
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g1) sender
  let srcCovers := fun key block => localCovers
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView key block = true
  let dstCovers := fun key block => localCovers
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView key block = true
  have hdst : Opposes dstCovers dstEarly dstLate dstRaw B := by
    simpa only [dstEarly, dstLate, dstRaw, dstCovers, opposing,
      decide_eq_true_eq] using hopposing
  have hSL : srcEarly ⊆ srcLate := by
    exact GradeCutoffMono.readyView_mono _ _ _ _
      (NamedOutageHistory.GuardedHelpers.early_g2_le_late_g2 S r) sender
  have hDL : dstEarly ⊆ dstLate := by
    exact GradeCutoffMono.readyView_mono _ _ _ _
      (NamedOutageHistory.GuardedHelpers.early_g1_le_late_g1 S r) sender
  let tr := crossReaderTokenTransport_of_delivery
    S rho core r delivery horizon v w hv hw B guard
  have hEqBack : ∀ k, EquivocationAt dstRaw k →
      EquivocationAt srcRaw k := by
    intro k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (tr.rawBack sender) hk
  have hsrc : Opposes srcCovers srcEarly srcLate srcRaw B := by
    by_cases hs : Opposes srcCovers srcEarly srcLate srcRaw B
    · exact hs
    · have hRound : ∀ k, (∀ u ∈ dstEarly, u.round ≤ k) →
          ∀ u ∈ srcEarly, u.round ≤ k := by
        intro k hk u hu
        obtain ⟨x, hx, hmax⟩ :=
          srcEarly.exists_max_image Token.round ⟨u, hu⟩
        have hxCover : srcCovers x.key B := by
          by_contra hnot
          exact hs (Or.inl ⟨x, hSL hx, hmax, hnot⟩)
        rcases tr.forward sender x hx hxCover with hxDst | hxEq
        · exact (hmax u hu).trans (hk x hxDst)
        · exact False.elim (hs (equivocation_opposes_of_round_bound
            srcCovers hmax (hEqBack _ hxEq)))
      rcases hdst with ⟨x, hx, hmax, hnot⟩ |
          ⟨x, hx, y, hy, hmax, hxy, hne⟩
      · rcases tr.lateBack sender x hx with hxSrc | hxEq
        · refine Or.inl ⟨x, hxSrc, hRound _ hmax, ?_⟩
          intro hxCover
          apply hnot
          exact (localCovers_iff_of_cross_late_ready S rho core r v w
            hv hw sender B x hxSrc hx).mp hxCover
        · exact equivocation_opposes_of_round_bound
            srcCovers (hRound _ hmax) hxEq
      · exact equivocation_opposes_of_round_bound srcCovers
          (hRound _ hmax)
          (hEqBack _ ⟨x, hx, y, hy, rfl, hxy.symm, hne⟩)
  simpa only [srcEarly, srcLate, srcRaw, srcCovers, opposing,
    decide_eq_true_eq] using hsrc

/-- Relative G2 at one honest domain reader is relative G1 at another. The
opposing set can only shrink and the positive set can only grow. -/
theorem storeGrade_g1_of_storeGrade_g2_cross_reader
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B : Block V)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 B = true)
    (guard : CrossReaderBodyReadyGuard S rho r v w B) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 B = true := by
  change gradeBool S.E
    (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g2) (late S.E S.hc r .g2) B = true at hgrade
  change gradeBool S.E
    (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) (late S.E S.hc r .g1) B = true
  simp only [gradeBool, decide_eq_true_eq] at hgrade ⊢
  have hOpp : (Finset.univ.filter fun sender => opposing
      (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1)
      sender B = true) ⊆
      Finset.univ.filter fun sender => opposing
        (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
        (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2)
        sender B = true := by
    intro sender hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ sender,
      opposing_g1_at_w_imp_opposing_g2_at_v S rho core r delivery
        horizon v w hv hw B guard sender (Finset.mem_filter.mp hs).2⟩
  have hPos : (Finset.univ.filter fun sender => positive
      (phaseRead S rho r .g2 v).st.core.toHealing.gradeView
      (phaseRead S rho r .g2 v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2)
      sender B = true) ⊆
      Finset.univ.filter fun sender => positive
        (phaseRead S rho r .g1 w).st.core.toHealing.gradeView
        (phaseRead S rho r .g1 w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1)
        sender B = true := by
    intro sender hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ sender,
      positive_g2_at_v_imp_positive_g1_at_w S rho core r delivery
        horizon v w hv hw B guard sender (Finset.mem_filter.mp hs).2⟩
  exact lt_of_le_of_lt (S.E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hgrade (S.E.electorate.weightOf_mono hPos))

structure G1G0CrossReaderBodyReadyGuard
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender u,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) sender →
    localCovers
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      u.confirmed B = true →
    DecoupledConsensusModel.Protocol.bodyReady
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g0 target).st.core.F
      (early S.E S.hc r .g0) u = true
  backward : ∀ sender u,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g0 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g0) sender →
    DecoupledConsensusModel.Protocol.bodyReady
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 source).st.core.F
      (late S.E S.hc r .g1) u = true

/-- The cap facts needed for the two body-open checks. They mention
only the heads that occur in the source and target interpreted inputs. -/
structure G1G0CrossReaderFinalizedBelow
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender u root H,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) sender →
    localCovers
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      u.confirmed B = true →
    u.confirmed = some root →
    Block.find?
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView.T root =
        some H →
    Block.Preceq (phaseRead S rho r .g0 target).st.core.F H
  backward : ∀ sender u root H,
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g0 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g0) sender →
    u.confirmed = some root →
    Block.find?
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView.T root =
        some H →
    Block.compatible H (phaseRead S rho r .g1 source).st.core.F = true

/-- Finality safety and one-delay evidence relay supply the reverse reader
guard. The forward guard is the selected-block cap from the consumer. -/
theorem g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
    (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round}
    (hgst : S.E.t_GST ≤ early S.E S.hc r .g1)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
        (phaseRead S rho r .g1 source).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g1) sender →
      localCovers
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
        u.confirmed B = true →
      u.confirmed = some root →
      Block.find?
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView.T root =
          some H →
      Block.Preceq (phaseRead S rho r .g0 target).st.core.F H) :
    G1G0CrossReaderFinalizedBelow S rho r source target B := by
  have hgstDomain : S.E.t_GST ≤ domain S.E S.hc r .g1 :=
    hgst.trans (early_g1_le_domain_g1 S r)
  have hg0Horizon : domain S.E S.hc r .g0 ≤ rho.horizon := horizon
  have hForder := finalized_preceq_of_evidence_delivered
    S adm hsb hsource htarget hgstDomain
      (domain_g1_add_delta_eq_g0 S r) hg0Horizon
  refine ⟨hforward, ?_⟩
  intro sender u root H hu hconf hfind
  obtain ⟨-, hready⟩ := Finset.mem_filter.mp hu
  simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf, hfind,
    Bool.and_eq_true] at hready
  have hcompat := hready.2
  simp only [Block.compatible, Bool.or_eq_true] at hcompat ⊢
  rcases hcompat with hHF | hFH
  · rcases Block.preceq_linear hForder hHF with hsourceH | hHsource
    · exact Or.inr hsourceH
    · exact Or.inl hHsource
  · exact Or.inr (Block.preceq_trans hForder hFH)

#print axioms g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay

private theorem post_event_body_at_strict_read
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (cut : Time) (reader : V)
    {j : Nat} {e : NamedEvent V} {H : NamedBlock V}
    (he : rho.events[j]? = some e) (ht : e.time < cut)
    (hheld : H ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  have hindex := post_index_le_strict_filter_length rho core.sorted cut he ht
  have hcarry := NamedBodyRetention.stateBefore_bodies_mono
    S rho reader hindex hheld
  unfold NamedRun.stateBeforeTime
  rw [strict_filter_eq_take rho core.sorted cut]
  exact hcarry

private theorem strict_read_eq_index_local
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (strict_filter_eq_take rho core.sorted t)

omit [DecidableEq V] [Fintype V] in
private theorem strict_lengths_mono_local
    (rho : NamedRun V) {early late : Time} (ht : early ≤ late) :
    (rho.events.filter (fun e => decide (e.time < early))).length ≤
      (rho.events.filter (fun e => decide (e.time < late))).length := by
  have hsub := List.Sublist.filter
    (fun e : NamedEvent V => decide (e.time < late))
    (List.filter_sublist
      (p := fun e : NamedEvent V => decide (e.time < early))
      (l := rho.events))
  have hs : (rho.events.filter
      (fun e => decide (e.time < early))).filter
        (fun e => decide (e.time < late)) =
      rho.events.filter (fun e => decide (e.time < early)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hearly : e.time < early := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hearly.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

private theorem strict_body_stamp_carry_local
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (reader : V)
    {early late : Time} (ht : early ≤ late) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho early reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho late reader).st.bodies ∧
      (NamedRun.stateBeforeTime S rho late reader).st.core.timestamp_block
          H.erase =
        (NamedRun.stateBeforeTime S rho early reader).st.core.timestamp_block
          H.erase := by
  rw [strict_read_eq_index_local S rho core early] at hH
  rw [strict_read_eq_index_local S rho core late,
    strict_read_eq_index_local S rho core early]
  exact NamedBlockStamp.stateBefore_body_stamp_mono S rho reader
    (strict_lengths_mono_local rho ht) hH

/-- Relay a head body to the later cutoff. Compatibility with the receiver's
later finalized root is enough: if the receiver has already finalized past
the head, parent closure shows that it already holds the head. -/
private theorem compatible_head_body_at_read_after_gst
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (source : V) (hsource : source ∈ rho.honest)
    (reader : V) (hreader : reader ∈ rho.honest) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hHsource :
      H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead)
    (hCut : targetEarly ≤ rho.horizon)
    (hcompat : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F = true) :
    H ∈ (NamedRun.stateBeforeTime S rho targetRead reader).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho targetRead reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho targetRead reader).st.core.T
        H.erase.root = some H.erase := by
  have hHscope : NamedRun.blockInRun S rho H := by
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho core.sorted sourceCut
    rw [hn] at hHsource
    exact Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hHsource
  have hEarly : H ∈
      (NamedRun.stateBeforeTime S rho targetEarly reader).st.bodies := by
    by_cases hgen : H = NamedBlock.genesis
    · subst H
      exact (Proofs.NamedRuntime.stateBeforeTime_invariants
        S rho targetEarly reader).1.1.1.2.2.1.1
    · obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho core.sorted sourceCut
      rw [hn] at hHsource
      rcases NamedOutageProvenance.held_block_origin
          S rho n source hHsource with hgen' | ⟨i, hi, ta, hacc⟩
      · exact False.elim (hgen hgen')
      · obtain ⟨eSource, heSource, -, htSource⟩ := hacc.1.2
        have hta : ta < sourceCut := by
          simpa only [htSource] using hbefore i eSource hi heSource
        have hmax : max ta S.E.t_GST ≤ max sourceCut S.E.t_GST :=
          max_le_max hta.le (le_refl _)
        have htaDeadline : max ta S.E.t_GST + S.E.Δ ≤ targetEarly :=
          (add_le_add hmax (le_refl _)).trans hDeadline
        have htaEarly : ta < targetEarly :=
          (le_max_left ta S.E.t_GST).trans_lt
            ((lt_add_of_pos_right _ S.E.Δ_pos).trans_le htaDeadline)
        by_cases hskip : H ∈
            (NamedRun.stateBefore S rho (i + 1) reader).st.bodies
        · exact post_event_body_at_strict_read
            S rho core targetEarly reader heSource
              (by simpa only [htSource] using htaEarly) hskip
        · have hmissing : NamedReceipt.processed
              (NamedRun.stateBefore S rho (i + 1) reader).st
                (.block H) = false := by
            simpa only [NamedReceipt.processed, decide_eq_false_iff_not]
              using hskip
          have hcompatRead : Block.compatible
              (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase = true := by
            have h := hcompat
            simp only [Block.compatible, Bool.or_eq_true] at h ⊢
            exact h.symm
          have hguard := not_excludes_of_compatible_later_time S rho core.sorted
            (htaDeadline.trans hOrder) hcompatRead
          obtain ⟨td, hlo, hhi, j, hcall⟩ :=
            core.toNamedSynchrony.relay_block source hsource i H ta hacc
              reader hreader hmissing (htaDeadline.trans hCut) hguard
          obtain ⟨e, he, -, het⟩ := hcall.2
          have htdEarly : td < targetEarly := hhi.trans_le htaDeadline
          have heEarly : e.time < targetEarly := by
            simpa only [het] using htdEarly
          have heRead : e.time < targetRead := heEarly.trans_le hOrder
          have hindex := post_index_le_strict_filter_length
            rho core.sorted targetRead he heRead
          have hFmono := Proofs.NamedRuntime.stateBefore_F_mono S rho reader
            ((Nat.le_succ j).trans hindex)
          by_cases hheldCall :
              H ∈ (NamedRun.stateBefore S rho j reader).st.bodies
          · have hpost := NamedBodyRetention.stateBefore_bodies_mono
              S rho reader (Nat.le_succ j) hheldCall
            exact post_event_body_at_strict_read
              S rho core targetEarly reader he heEarly hpost
          · have hFcall : Block.Preceq
                (NamedRun.stateBefore S rho j reader).st.core.F H.erase := by
              have hfuture : Block.Preceq
                  (NamedRun.stateBefore S rho j reader).st.core.F
                  (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F := by
                simpa only [strict_read_eq_index_local S rho core targetRead]
                  using hFmono
              simp only [Block.compatible, Bool.or_eq_true] at hcompat
              rcases hcompat with hHF | hFH
              · rcases Block.preceq_linear hfuture hHF with h | h
                · exact h
                · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBefore
                    S rho j reader
                  have hpc := Proofs.NamedStoreBridge.parentClosed_stateBefore
                    S rho j reader
                  have hraw : H.erase ∈
                      (NamedRun.stateBefore S rho j reader).st.core.T :=
                    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
                      H.erase _ hFmem h
                  obtain ⟨K, hK, hKErase⟩ :=
                    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
                      S rho j reader hraw
                  have hKscope : NamedRun.blockInRun S rho K :=
                    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hK
                  have hKH : K = H := runBlock_unique_of_erase_eq
                    core.toNamedRootCollisionFree hKscope hHscope hKErase
                  subst K
                  exact False.elim (hheldCall hK)
              · exact Block.preceq_trans hfuture hFH
            have hpost :=
              NamedRelayGuards.handled_block_held_of_finalized_prefix
                S rho core.toNamedScheduleWellFormed
                  core.toNamedDeliveryWellFormed
                  core.toNamedRootCollisionFree hacc hcall hlo hFcall
            exact post_event_body_at_strict_read
              S rho core targetEarly reader he heEarly hpost
  have hStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
    S rho core.toNamedScheduleWellFormed reader targetEarly H hEarly
  obtain ⟨hHeld, hCarry⟩ := strict_body_stamp_carry_local
    S rho core reader hOrder H hEarly
  refine ⟨hHeld, ?_, ?_⟩
  · unfold stampedBefore at hStamp ⊢
    rw [hCarry]
    exact hStamp
  · simpa only [Proofs.NamedWire.erase_root] using
      (held_find_at_strict S rho core hreader targetRead H hHeld)

/-- Transport the referenced named bodies at the two fixed cutoffs, then use
the caller's finality cap to discharge `bodyReady` at the other reader. -/
theorem g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r)
    (hgst : S.E.t_GST ≤ early S.E S.hc r .g1)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hbelow : G1G0CrossReaderFinalizedBelow S rho r source target B) :
    G1G0CrossReaderBodyReadyGuard S rho r source target B := by
  have hearlyHorizon : early S.E S.hc r .g0 ≤ rho.horizon :=
    (early_g0_le_domain_g0 S r).trans horizon
  have hlateHorizon : late S.E S.hc r .g1 ≤ rho.horizon :=
    (late_g1_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  refine ⟨?_, ?_⟩
  · intro sender u hu hcover
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (phaseRead S rho r .g1 source).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈ (phaseRead S rho r .g1 source).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g1) source).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHearly : Hn ∈ (NamedRun.stateBeforeTime S rho
            (early S.E S.hc r .g1) source).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (early_g1_public S r hr)
            hHbody
          simpa only [hHnErase] using hstamp
        have hdeadline : max (early S.E S.hc r .g1) S.E.t_GST + S.E.Δ ≤
            early S.E S.hc r .g0 := by
          rw [max_eq_left hgst, early_g1_add_delta_eq_g0]
        have hFH : Block.Preceq
            (phaseRead S rho r .g0 target).st.core.F Hn.erase := by
          rw [hHnErase]
          exact hbelow.forward sender u root H hu hcover hconf hfind
        obtain ⟨-, hstampTarget, hfindTarget⟩ :=
          NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
            S rho core source hsource target htarget Hn
            (early S.E S.hc r .g1) (early S.E S.hc r .g0)
            (domain S.E S.hc r .g0) hHearly hdeadline
            (early_g0_le_domain_g0 S r)
            hearlyHorizon hFH
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindTarget' : Block.find?
            (phaseRead S rho r .g0 target).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [phaseRead, Proofs.NamedWire.erase_root] using hfindTarget
        change (match Block.find?
          (phaseRead S rho r .g0 target).st.core.T root with
          | none => false
          | some head => stampedBefore
              (phaseRead S rho r .g0 target).st.core.timestamp_block
              (early S.E S.hc r .g0) head &&
            Block.compatible head
              (phaseRead S rho r .g0 target).st.core.F) = true
        rw [← hroot, hfindTarget', Bool.and_eq_true]
        refine ⟨hstampTarget, ?_⟩
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hFH
  · intro sender u hu
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (phaseRead S rho r .g0 target).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈ (phaseRead S rho r .g0 target).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g0) target).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHlate : Hn ∈ (NamedRun.stateBeforeTime S rho
            (late S.E S.hc r .g0) target).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (late_g0_public S r hr) hHbody
          simpa only [hHnErase] using hstamp
        have hgstLate : S.E.t_GST ≤ late S.E S.hc r .g0 := by
          exact hgst.trans (by
            simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
            linarith [S.E.Δ_pos])
        have hdeadline : max (late S.E S.hc r .g0) S.E.t_GST + S.E.Δ ≤
            late S.E S.hc r .g1 := by
          rw [max_eq_left hgstLate, late_g0_add_delta_eq_g1]
        have hcompatSource : Block.compatible Hn.erase
            (phaseRead S rho r .g1 source).st.core.F = true := by
          rw [hHnErase]
          exact hbelow.backward sender u root H hu hconf hfind
        obtain ⟨hHsource, hstampSource, hfindSource⟩ :=
          compatible_head_body_at_read_after_gst
            S rho core target htarget source hsource Hn
              (late S.E S.hc r .g0) (late S.E S.hc r .g1)
              (domain S.E S.hc r .g1) hHlate hdeadline
              (late_g1_le_domain_g1 S r) hlateHorizon hcompatSource
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindSource' : Block.find?
            (phaseRead S rho r .g1 source).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [phaseRead, Proofs.NamedWire.erase_root] using hfindSource
        change (match Block.find?
          (phaseRead S rho r .g1 source).st.core.T root with
          | none => false
          | some head => stampedBefore
              (phaseRead S rho r .g1 source).st.core.timestamp_block
              (late S.E S.hc r .g1) head &&
            Block.compatible head
              (phaseRead S rho r .g1 source).st.core.F) = true
        rw [← hroot, hfindSource', Bool.and_eq_true]
        refine ⟨hstampSource, ?_⟩
        exact hcompatSource

#print axioms g1G0CrossReaderBodyReadyGuard_of_finalizedBelow

private structure G1G0CrossReaderTokenTransport
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (source target : V) (B : Block V) : Prop where
  forward : ∀ sender x,
    x ∈ readyView
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      (phaseRead S rho r .g1 source).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) sender →
    localCovers
      (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
      x.key B = true →
    x ∈ readyView
        (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
        (phaseRead S rho r .g0 target).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g0) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g0) sender) x.round
  lateBack : ∀ sender x,
    x ∈ readyView
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g0 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g0) sender →
    x ∈ readyView
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
        (phaseRead S rho r .g1 source).st.core.F
        S.hc.η_SG r (late S.E S.hc r .g1) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g1) sender) x.round
  rawBack : ∀ sender x,
    x ∈ rawView
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      S.hc.η_SG r (late S.E S.hc r .g0) sender →
    x ∈ rawView
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
        S.hc.η_SG r (late S.E S.hc r .g1) sender ∨
      EquivocationAt
        (rawView
          (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g1) sender) x.round

private theorem g1G0CrossReaderTokenTransport_of_delivery
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : G1G0TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (source target : V) (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) (B : Block V)
    (guard : G1G0CrossReaderBodyReadyGuard S rho r source target B) :
    G1G0CrossReaderTokenTransport S rho r source target B := by
  have hearlyHorizon : early S.E S.hc r .g0 ≤ rho.horizon :=
    (early_g0_le_domain_g0 S r).trans horizon
  have hlateHorizon : late S.E S.hc r .g1 ≤ rho.horizon :=
    (late_g1_le_domain_g1 S r).trans
      ((domain_g1_le_domain_g0 S r).trans horizon)
  refine ⟨?_, ?_, ?_⟩
  · intro sender x hx hcover
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hraw, -⟩ := Finset.mem_filter.mp hu
    have hval : u.val_index = sender := (Finset.mem_filter.mp hraw).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g1_raw_input_source_acceptance S rho
        core.toNamedScheduleWellFormed source r sender u hraw
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hrelay := accepted_sg_vote_or_equiv_at_g0_of_relay_local
      S rho r core hacc hbefore hwindow (fun reader hreader hmissing =>
        delivery.earlyAttest source hsource i a accepted hacc hbefore
          reader hreader hmissing hearlyHorizon) target htarget
    simp only [hproj, hidx] at hrelay
    rcases hrelay with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (Finset.mem_filter.mpr ⟨hexact, guard.forward sender u hu hcover⟩))
    · have hmono := GradeCutoffMono.rawView_mono
        (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
        S.hc.η_SG r
        (early_g0_le_late_g0 S r)
        sender
      exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        hmono (Finset.mem_image_of_mem _ hleft),
        DecoupledConsensusModel.Protocol.token right,
        hmono (Finset.mem_image_of_mem _ hright), hlr.trans hround,
        hrr.trans hround, hne⟩
  · intro sender x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hraw, -⟩ := Finset.mem_filter.mp hu
    have hval : u.val_index = sender := (Finset.mem_filter.mp hraw).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g0_late_raw_input_acceptance
        S rho core.toNamedScheduleWellFormed target r sender u hraw
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hone :=
      accepted_sg_vote_or_equiv_at_g1_late_of_relay_local
        S rho r core hacc hbefore hwindow
        (fun reader hreader hmissing =>
          delivery.lateAttest target htarget i a accepted hacc hbefore
            reader hreader hmissing hlateHorizon) source hsource
    simp only [hproj, hidx] at hone
    rcases hone with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (Finset.mem_filter.mpr ⟨hexact, guard.backward sender u hu⟩))
    · exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        Finset.mem_image_of_mem _ hleft, DecoupledConsensusModel.Protocol.token right,
        Finset.mem_image_of_mem _ hright, hlr.trans hround,
        hrr.trans hround, hne⟩
  · intro sender x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hval : u.val_index = sender := (Finset.mem_filter.mp hu).2.1
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      NamedRawSource.g0_late_raw_input_acceptance
        S rho core.toNamedScheduleWellFormed target r sender u hu
    have hround : a.round = u.round :=
      congrArg Protocol.SGVote.round hproj
    have hidx : a.val_index = sender :=
      (congrArg Protocol.SGVote.val_index hproj).trans hval
    have hone :=
      accepted_sg_vote_or_equiv_at_g1_late_of_relay_local
        S rho r core hacc hbefore hwindow
        (fun reader hreader hmissing =>
          delivery.lateAttest target htarget i a accepted hacc hbefore
            reader hreader hmissing hlateHorizon) source hsource
    simp only [hproj, hidx] at hone
    rcases hone with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl (Finset.mem_image_of_mem _ hexact)
    · exact Or.inr ⟨DecoupledConsensusModel.Protocol.token left,
        Finset.mem_image_of_mem _ hleft, DecoupledConsensusModel.Protocol.token right,
        Finset.mem_image_of_mem _ hright, hlr.trans hround,
        hrr.trans hround, hne⟩


private theorem localCovers_iff_of_g1G0_target_ready
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (r : Round) (source target : V) (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) (sender : V) (B : Block V)
    (guard : G1G0CrossReaderBodyReadyGuard S rho r source target B)
    (x : Token (Option BlockId))
    (htargetReady : x ∈ readyView
      (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
      (phaseRead S rho r .g0 target).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g0) sender) :
    (localCovers
        (phaseRead S rho r .g1 source).st.core.toHealing.gradeView
        x.key B = true ↔
      localCovers
        (phaseRead S rho r .g0 target).st.core.toHealing.gradeView
        x.key B = true) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htargetReady
  obtain ⟨-, hbodyTarget⟩ := Finset.mem_filter.mp hu
  have hbodySource := guard.backward sender u hu
  cases hconf : u.confirmed with
  | none =>
      simp [DecoupledConsensusModel.Protocol.token, localCovers, Protocol.head_covers, hconf]
  | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hbodySource hbodyTarget
      cases hfindSource : Block.find?
          (phaseRead S rho r .g1 source).st.core.toHealing.gradeView.T root with
      | none =>
          rw [hfindSource] at hbodySource
          exact absurd hbodySource (by simp)
      | some H =>
          cases hfindTarget : Block.find?
              (phaseRead S rho r .g0 target).st.core.toHealing.gradeView.T
                root with
          | none =>
              rw [hfindTarget] at hbodyTarget
              exact absurd hbodyTarget (by simp)
          | some K =>
              have hHK :=
                NamedOutageHistory.GuardedHelpers.find_agree S rho core
                  source target hsource htarget
                  (domain S.E S.hc r .g1) (domain S.E S.hc r .g0)
                  root hfindSource hfindTarget
              subst K
              simp [DecoupledConsensusModel.Protocol.token, localCovers,
                Protocol.head_covers, hconf, hfindSource, hfindTarget]

/-- Relative G1 at one honest domain reader is relative G0 at another. -/
theorem storeGrade_g0_of_storeGrade_g1_cross_reader
    (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho)
    (r : Round) (delivery : G1G0TwoCutoffDelivery S rho r)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B : Block V)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) v).st r .g1 B = true)
    (guard : G1G0CrossReaderBodyReadyGuard S rho r v w B) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) w).st r .g0 B = true := by
  let srcEarly := fun sender => readyView
    (phaseRead S rho r .g1 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 v).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) sender
  let srcLate := fun sender => readyView
    (phaseRead S rho r .g1 v).st.core.toHealing.gradeView
    (phaseRead S rho r .g1 v).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g1) sender
  let srcRaw := fun sender => rawView
    (phaseRead S rho r .g1 v).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g1) sender
  let dstEarly := fun sender => readyView
    (phaseRead S rho r .g0 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g0 w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g0) sender
  let dstLate := fun sender => readyView
    (phaseRead S rho r .g0 w).st.core.toHealing.gradeView
    (phaseRead S rho r .g0 w).st.core.F S.hc.η_SG r
    (late S.E S.hc r .g0) sender
  let dstRaw := fun sender => rawView
    (phaseRead S rho r .g0 w).st.core.toHealing.gradeView
    S.hc.η_SG r (late S.E S.hc r .g0) sender
  let srcCovers := fun key block => localCovers
    (phaseRead S rho r .g1 v).st.core.toHealing.gradeView key block = true
  let dstCovers := fun key block => localCovers
    (phaseRead S rho r .g0 w).st.core.toHealing.gradeView key block = true
  have hsrc : DecoupledConsensusModel.Protocol.grade S.E.electorate.weight
      srcCovers srcEarly srcLate srcRaw B := by
    have hsrc' :=
      (NamedOutageHistory.GuardedHelpers.storeGrade_iff S
        (readAt S rho (domain S.E S.hc r .g1) v).st r .g1 B).mp hgrade
    simpa only [srcCovers, srcEarly, srcLate, srcRaw, phaseRead, PhaseGrades.readAt]
      using hsrc'
  let tr := g1G0CrossReaderTokenTransport_of_delivery
    S rho core r delivery horizon v w hv hw B guard
  have hEqBack : ∀ sender k, EquivocationAt (dstRaw sender) k →
      EquivocationAt (srcRaw sender) k := by
    intro sender k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (tr.rawBack sender) hk
  have htransport : DecoupledConsensusModel.Protocol.grade S.E.electorate.weight
      srcCovers dstEarly dstLate dstRaw B := by
    exact DecoupledConsensusModel.Protocol.grade_transport_with_cap
      (se := srcEarly) (sl := srcLate) (sr := srcRaw)
      (te := dstEarly) (tl := dstLate) (tr := dstRaw) (B := B)
      S.E.electorate.weight srcCovers
      (fun sender => GradeCutoffMono.readyView_mono _ _ _ _
        (NamedOutageHistory.GuardedHelpers.early_g1_le_late_g1 S r)
          sender)
      (fun sender =>
        GradeCutoffMono.readyView_subset_rawView _ _ _ _ _ sender)
      (fun sender => GradeCutoffMono.readyView_mono _ _ _ _
        (early_g0_le_late_g0 S r) sender)
      tr.forward tr.lateBack hEqBack hsrc
  have htarget : DecoupledConsensusModel.Protocol.grade S.E.electorate.weight
      dstCovers dstEarly dstLate dstRaw B := by
    exact NamedOutageHistory.GuardedHelpers.grade_congr
      S.E.electorate.weight srcCovers dstCovers
      (fun sender => GradeCutoffMono.readyView_mono _ _ _ _
        (early_g0_le_late_g0 S r) sender)
      (fun sender x hx =>
        localCovers_iff_of_g1G0_target_ready
          S rho core r v w hv hw sender B guard x hx)
      htransport
  apply (NamedOutageHistory.GuardedHelpers.storeGrade_iff S
    (readAt S rho (domain S.E S.hc r .g0) w).st r .g0 B).mpr
  simpa only [dstCovers, dstEarly, dstLate, dstRaw, phaseRead, PhaseGrades.readAt]
    using htarget

#print axioms positive_g2_at_v_imp_positive_g1_at_w
#print axioms opposing_g1_at_w_imp_opposing_g2_at_v
#print axioms storeGrade_g1_of_storeGrade_g2_cross_reader
#print axioms twoCutoffDelivery_of_core
#print axioms g1G0TwoCutoffDelivery_of_core
#print axioms g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
#print axioms g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
#print axioms storeGrade_g0_of_storeGrade_g1_cross_reader

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
