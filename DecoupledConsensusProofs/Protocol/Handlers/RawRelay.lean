module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Schedule.ReceiptCallsF1
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section

/-! Compiler-free arbitrary-sender raw vote-or-equivocation relay.
The copied SG metadata/clock helpers are private. Only the final query is public. -/
namespace DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

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

private theorem early_g2_delay_eq_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 + S.E.Δ = early S.E S.hc r .g1 := by
  unfold early Phase.earlyOffset
  ring

private theorem early_g1_lt_opening (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 < opening S.E S.hc r := by
  unfold early Phase.earlyOffset
  change opening S.E S.hc r + (-4 : Time) * S.E.Δ < opening S.E S.hc r
  have hneg : (-4 : Time) * S.E.Δ < 0 :=
    Int.mul_neg_of_neg_of_pos (by norm_num) S.E.Δ_pos
  calc
    opening S.E S.hc r + (-4 : Time) * S.E.Δ < opening S.E S.hc r + 0 :=
      (add_lt_add_iff_left _).2 hneg
    _ = opening S.E S.hc r := add_zero _


/-- The original full representative and its unchanged first stamp are
transported from this event's own post-index to the target strict read. -/
private theorem held_projection_raw_after_event (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round) (reader sender : V)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < early S.E S.hc r .g1) (b : NamedAttestation V)
    (hb : b ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows b.round)
    (hwindow : b.round ∈ Protocol.latest_window S.hc.η_SG r) (hval : b.val_index = sender) :
    let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) reader
    Protocol.sgVote b.erase ∈ DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
      S.hc.η_SG r (early S.E S.hc r .g1) sender := by
  let cut := domain S.E S.hc r .g1
  let n := NamedRun.stateBeforeTime S rho cut reader
  have hpostData := (data_at_event S rho sch he reader).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hpostData.2 b.round b hb
  have hcut : e.time < cut := by
    change e.time < opening S.E S.hc r + (0 : Int) * S.E.Δ
    simpa only [zero_mul, add_zero] using ht.trans (early_g1_lt_opening S r)
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
      (early S.E S.hc r .g1) = true := by
    simp only [hreceipt, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt ht)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  have hpool := NamedAdmission.pool_view_mem n.st hcoh.2.2.2.1 b hheld
  have hsg : Protocol.sgVote b.erase ∈ n.st.core.toHealing.gradeView.sg_votes b.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ?_, hval, hoccur⟩
  exact ⟨b.round, List.mem_toFinset.mpr hwindow, hsg⟩





/-- Cutoff-specific form of `accepted_sg_vote_or_equiv_at_g1_of_healthy`.
The caller supplies only the one relay fact used by this accepted row. -/
theorem accepted_sg_vote_or_equiv_at_g1_of_relay
    (S : Setup V) (rho : NamedRun V) (r : Round)
    (core : NamedAdmissibleCore S rho)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.attest a) ta)
    (hsourceCut : ta < early S.E S.hc r .g2)
    (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r)
    (relay : ∀ reader ∈ rho.honest,
      NamedReceipt.processed
          (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false →
        ∃ td, ta ≤ td ∧ td < early S.E S.hc r .g1 ∧
          ∃ j : Nat, NamedRun.actualHandlesAt S rho j reader (.attest a) td) :
    ∀ reader ∈ rho.honest,
      let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) reader
      let raw := DecoupledConsensusModel.Protocol.rawInputs n.st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g1) a.val_index
      Protocol.sgVote a.erase ∈ raw ∨
        ∃ left ∈ raw, ∃ right ∈ raw,
          left.round = a.round ∧ right.round = a.round ∧
          left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
          left.confirmed ≠ right.confirmed := by
  obtain ⟨sourceEvent, hsourceEvent, -, hsourceTime⟩ := hacc.1.2
  have htaEarly : ta < early S.E S.hc r .g1 :=
    hsourceCut.trans (by
      rw [← early_g2_delay_eq_g1 S r]
      exact lt_add_of_pos_right _ S.E.Δ_pos)
  have hsourceFloor :=
    source_acceptance_opening_le S rho core.toNamedScheduleWellFormed hacc
  intro reader hreader
  by_cases hskip : a ∈
      (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows a.round
  · apply Or.inl
    exact held_projection_raw_after_event S rho
      core.toNamedScheduleWellFormed r reader a.val_index hsourceEvent
      (by simpa only [hsourceTime] using htaEarly) a hskip hwindow rfl
  · have hmissing : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) reader).st (.attest a) = false := by
      simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
    obtain ⟨td, hlo, htdEarly, j, hcall⟩ := relay reader hreader hmissing
    have htdOpen : td < opening S.E S.hc r :=
      htdEarly.trans (early_g1_lt_opening S r)
    have hout := call_vote_or_equiv S rho core.toNamedScheduleWellFormed r
      hcall (hsourceFloor.trans hlo) htdOpen hwindow
    obtain ⟨e, he, _, het⟩ := hcall.2
    have heEarly : e.time < early S.E S.hc r .g1 := by
      simpa only [het] using htdEarly
    rcases hout with ⟨vote, hvote, hround, hval, hkey⟩ |
      ⟨left, right, hleft, hright, hlround, hrround, hlval, hrval, hkeys⟩
    · have hraw := held_projection_raw_after_event S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly vote
        hvote (by simpa only [hround] using hwindow) hval
      have hproj : Protocol.sgVote vote.erase = Protocol.sgVote a.erase := by
        change Protocol.SGVote.mk vote.val_index vote.round vote.confirmed =
          Protocol.SGVote.mk a.val_index a.round a.confirmed
        rw [hval, hround, hkey]
      exact Or.inl (by simpa only [hproj] using hraw)
    · have hlraw := held_projection_raw_after_event S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly left
        hleft (by simpa only [hlround] using hwindow) hlval
      have hrraw := held_projection_raw_after_event S rho
        core.toNamedScheduleWellFormed r reader a.val_index he heEarly right
        hright (by simpa only [hrround] using hwindow) hrval
      exact Or.inr ⟨Protocol.sgVote left.erase, hlraw,
        Protocol.sgVote right.erase, hrraw, hlround, hrround, hlval, hrval,
        hkeys⟩

#print axioms accepted_sg_vote_or_equiv_at_g1_of_relay






end DecoupledConsensusModel.Proofs.NamedRawRelay

end
