module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Schedule.ReceiptCallsF1
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section

/-! Compiler-free actual named SG row/stamp transport. No body open,
P coverage or positive-support conclusion is included in this gate. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
variable {V : Type} [DecidableEq V] [Fintype V]

def Carry (before after : Protocol.NamedStore V) : Prop :=
  ∀ a : NamedAttestation V, a ∈ before.sg_rows a.round →
    a ∈ after.sg_rows a.round ∧
      after.core.timestamp_sg_vote (Protocol.sgVote a.erase) =
        before.core.timestamp_sg_vote (Protocol.sgVote a.erase)

omit [DecidableEq V] [Fintype V] in
theorem carry_refl (st : Protocol.NamedStore V) : Carry st st :=
  fun _ ha => ⟨ha, rfl⟩

omit [DecidableEq V] [Fintype V] in
theorem carry_trans {st mid out : Protocol.NamedStore V}
    (h : Carry st mid) (k : Carry mid out) : Carry st out := by
  intro a ha
  obtain ⟨hm, hs⟩ := h a ha
  obtain ⟨ho, ht⟩ := k a hm
  exact ⟨ho, ht.trans hs⟩

omit [DecidableEq V] [Fintype V] in
theorem carry_fields {st out : Protocol.NamedStore V}
    (hr : out.sg_rows = st.sg_rows)
    (ht : out.core.timestamp_sg_vote = st.core.timestamp_sg_vote) : Carry st out := by
  intro a ha
  exact ⟨by simpa only [hr] using ha, congrFun ht _⟩

omit [Fintype V] in
theorem finality_stamp (st : Protocol.Store V) (sigma : Protocol.ChainState V) :
    (Protocol.update_finality st sigma).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

theorem gf_checked_stamp (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> rfl

theorem gf_fold_stamp (E : Env V) (st : Protocol.Store V) (rows : List (GoldfishVote V)) :
    (rows.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_sg_vote =
      st.timestamp_sg_vote := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, gf_checked_stamp]

theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

theorem core_block_stamp (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
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

theorem row_carry (S : Setup V) (st : Protocol.NamedStore V) (incoming : NamedAttestation V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedAdmission.admit_row S.hc st incoming) := by
  intro a ha
  exact ⟨NamedReceiptCallsF1.admit_row_mem_mono S.hc st incoming a ha,
    NamedAdmission.existing_row_stamp S.hc st hcoh.2.2.2.1 incoming a ha⟩

theorem rows_carry (S : Setup V) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V))
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows generalizing st with
  | nil => exact carry_refl st
  | cons a rows ih =>
    exact carry_trans (row_carry S st a hcoh)
      (ih _ (NamedAdmission.coherent_admit_row S.E S.hc S.cfg st a hcoh))

theorem block_carry (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hcore := carry_fields (core_block_rows S st B) (core_block_stamp S st B)
  have hc := NamedStore.coherent_process_block S.E S.hc S.cfg st B hcoh
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact carry_trans hcore (rows_carry S _ B.attestations hc)
  · exact hcore

theorem propose_coherent (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Proofs.NamedStore.Coherent S.E S.cfg
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact hcoh
  · exact NamedAdmission.coherent_on_block .alsoCarried S.E S.hc S.cfg st _ hcoh

theorem propose_carry (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact carry_refl st
  · exact block_carry S st _ hcoh

theorem gf_carry (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    Carry st (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact carry_fields rfl (gf_checked_stamp S.E _ _)
  · exact carry_refl _

theorem confirmation_carry (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) :
    Carry st (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) :=
  carry_fields rfl rfl

theorem tick_carry (gc : Protocol.GradeContract V) (S : Setup V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  have hc0 : Proofs.NamedStore.Coherent S.E S.cfg st0 := NamedStore.coherent_clock S.E S.cfg st t hcoh
  have hc1 : Proofs.NamedStore.Coherent S.E S.cfg st1 := by
    dsimp only [st1]; split_ifs
    · exact propose_coherent gc S nd st0 hc0
    · exact hc0
  have h01 : Carry st st1 := by
    have h0 : Carry st st0 := carry_fields rfl rfl
    dsimp only [st1]; split_ifs
    · exact carry_trans h0 (propose_carry gc S nd st0 hc0)
    · exact h0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  have hc2 : Proofs.NamedStore.Coherent S.E S.cfg st2 := by
    dsimp only [st2]; split_ifs
    · exact NamedDuties.coherent_goldfish_vote gc S.E S.hc S.cfg nd st1 hc1
    · exact hc1
  have h02 : Carry st st2 := by
    dsimp only [st2]; split_ifs
    · exact carry_trans h01 (gf_carry gc S nd st1)
    · exact h01
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hc3 : Proofs.NamedStore.Coherent S.E S.cfg st3 := by
    dsimp only [st3]; split_ifs
    · exact NamedDuties.coherent_confirmation gc S.E S.hc S.cfg st2 (s - 1) hc2
    · exact hc2
  have h03 : Carry st st3 := by
    dsimp only [st3]; split_ifs
    · exact carry_trans h02 (confirmation_carry gc S st2 (s - 1))
    · exact h02
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧ nd.awake (S.hc.round_of st3.core.s) = true
        then (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact carry_trans h03 (row_carry S st3 _ hc3)
  · exact h03

theorem process_carry (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) : Carry st (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_carry S st B hcoh
  | gfVote u => exact carry_fields rfl (gf_checked_stamp S.E st.core u)
  | attest a => exact row_carry S st a hcoh

theorem carry_succ (S : Setup V) (rho : NamedRun V) (i : Nat) (reader : V) :
    Carry (NamedRun.stateBefore S rho i reader).st
      (NamedRun.stateBefore S rho (i + 1) reader).st := by
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1
  rw [Proofs.NamedRuntime.stateBefore_succ]
  cases he : rho.events[i]? with
  | none => exact carry_refl _
  | some e =>
    change Carry (NamedRun.stateBefore S rho i reader).st
      (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
    by_cases hv : reader = e.node
    · cases e with
      | tick v t =>
        change reader = v at hv
        subst v
        rw [Proofs.NamedRuntime.step_tick]
        exact tick_carry _ S (S.node reader) _ _ t hcoh
      | deliver v o t =>
        change reader = v at hv
        subst v
        rw [Proofs.NamedRuntime.step_deliver]
        exact process_carry S _ o hcoh
    · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
      exact carry_refl _

theorem stateBefore_sg_row_stamp_mono (S : Setup V) (rho : NamedRun V) (reader : V)
    {i j : Nat} (hij : i ≤ j) {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBefore S rho i reader).st.sg_rows a.round) :
    a ∈ (NamedRun.stateBefore S rho j reader).st.sg_rows a.round ∧
      (NamedRun.stateBefore S rho j reader).st.core.timestamp_sg_vote (Protocol.sgVote a.erase) =
        (NamedRun.stateBefore S rho i reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase) := by
  have h : Carry (NamedRun.stateBefore S rho i reader).st
      (NamedRun.stateBefore S rho j reader).st := by
    induction j, hij using Nat.le_induction with
    | base => exact carry_refl _
    | succ j hij ih => exact carry_trans ih (carry_succ S rho j reader)
  exact h a ha

/-- Every held row is in its own bucket and has a real first projected
stamp at or before this fixed bound. No body condition is included. -/
def Data (bound : Time) (st : Protocol.NamedStore V) : Prop :=
  st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
      st.core.timestamp_sg_vote (Protocol.sgVote a.erase) = some (stamp : Stamp)

omit [DecidableEq V] [Fintype V] in
theorem data_fields {bound : Time} {st out : Protocol.NamedStore V}
    (h : Data bound st) (hr : out.sg_rows = st.sg_rows)
    (hs : out.core.timestamp_sg_vote = st.core.timestamp_sg_vote)
    (ht : out.core.t = st.core.t) : Data bound out := by
  exact ⟨by simpa only [ht] using h.1, by simpa only [hr, hs] using h.2⟩

omit [Fintype V] in
theorem row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

theorem row_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
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

theorem rows_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hd : Data bound st) : Data bound (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows generalizing st with
  | nil => exact hd
  | cons a rows ih =>
    exact ih _ (NamedAdmission.coherent_admit_row S.E S.hc S.cfg st a hcoh)
      (row_data S bound st a hcoh hd)

theorem core_block_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hd : Data bound st) :
    Data bound (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) :=
  data_fields hd (core_block_rows S st B) (core_block_stamp S st B)
    (NamedAdmission.process_block_clock S.E S.hc S.cfg st B).1

theorem block_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hc := NamedStore.coherent_process_block S.E S.hc S.cfg st B hcoh
  have hdcore := core_block_data S bound st B hd
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_data S bound _ B.attestations hc hdcore
  · exact hdcore

theorem propose_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact hd
  · exact block_data S bound st _ hcoh hd

theorem gf_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact data_fields hd rfl (gf_checked_stamp S.E _ _)
      (on_goldfish_vote_checked_time S.E _ _)
  · exact hd

theorem confirmation_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
    (st : Protocol.NamedStore V) (s : Slot) (hd : Data bound st) :
    Data bound (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) :=
  data_fields hd rfl rfl rfl

theorem clock_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (t : Time) (ht : t ≤ bound) (hd : Data bound st) :
    Data bound (Protocol.NamedStore.setClock S.E st t) := ⟨ht, hd.2⟩

/-- Fixed-time scheduler induction used only with the concrete facts below. -/
theorem tick_preserves (gc : Protocol.GradeContract V) (S : Setup V)
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

theorem tick_data (gc : Protocol.GradeContract V) (S : Setup V) (bound : Time)
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

theorem process_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (o : NamedObject V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (hd : Data bound st) :
    Data bound (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_data S bound st B hcoh hd
  | gfVote u =>
    exact data_fields hd rfl (gf_checked_stamp S.E st.core u)
      (on_goldfish_vote_checked_time S.E st.core u)
  | attest a => exact row_data S bound st a hcoh hd

theorem prefix_data (S : Setup V) (rho : NamedRun V) (bound : Time) (hzero : 0 ≤ bound)
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
theorem event_time_le (rho : NamedRun V)
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

theorem data_at_event (S : Setup V) (rho : NamedRun V)
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

theorem stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
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


theorem emitted_block_due (gc : Protocol.GradeContract V)
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

theorem handle_event_time (S : Setup V) (rho : NamedRun V)
    {i : Nat} {reader : V} {o : NamedObject V} {td : Time} {e : NamedEvent V}
    (hcall : NamedRun.actualHandlesAt S rho i reader o td)
    (he : rho.events[i]? = some e) : e.time = td := by
  obtain ⟨f, hf, _, ht⟩ := hcall.2
  have hef : e = f := Option.some.inj (he.symm.trans hf)
  exact (congrArg NamedEvent.time hef).trans ht

theorem tick_le_clock_before_delivery (S : Setup V) (rho : NamedRun V)
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

theorem delivery_round (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {i : Nat} {reader : V} {o : NamedObject V}
    {td : Time} (q : Round) (he : rho.events[i]? = some (.deliver reader o td))
    (hlo : S.a q ≤ td) (hhi : td < S.a q + S.E.Δ) :
    S.hc.round_of (NamedRun.stateBefore S rho i reader).st.core.s = q := by
  have hmem := List.mem_of_getElem? he
  have hr : reader ∈ rho.honest := sch.honest_only _ hmem
  have htick := sch.tick_total reader hr (S.a q) (Proofs.HealingLemmas.publicTime_a S q)
    (Proofs.HealingLemmas.a_nonneg S q) (hlo.trans (sch.in_horizon _ hmem).2)
  have hclock := tick_le_clock_before_delivery S rho sch he htick hlo
  have hup := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted he
    (sch.in_horizon _ hmem).1 reader
  rw [stateBefore_slot_clock, Proofs.HealingLemmas.slotOf_of_between_a S q hclock (hup.trans_lt hhi),
    Proofs.HealingLemmas.round_of_opening_succ]

theorem tick_rows_after_proposal (gc : Protocol.GradeContract V) (S : Setup V)
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
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧ nd.awake (S.hc.round_of st3.core.s) = true
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

theorem block_call_rows_after_event (S : Setup V) (rho : NamedRun V)
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

theorem action_tick_store (S : Setup V) (reader : V) (before : NamedNodeState V)
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
  have hp : ¬ (0 < S.E.slotOf (S.a q) ∧ S.a q = Protocol.proposal_time S.E (S.E.slotOf (S.a q)) ∧
      S.E.proposer (S.E.slotOf (S.a q)) = (S.node reader).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a q) ∧ S.a q = Protocol.vote_time S.E (S.E.slotOf (S.a q))) := by
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

/-- This witness is produced from the actual direct/self/F1 call. Its
private inclusion function is not an input to either public query. -/
theorem actual_call_input (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {i : Nat} {reader : V}
    {a : NamedAttestation V} {td : Time}
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td)
    (hlo : S.a a.round ≤ td) (hhi : td < S.a a.round + S.E.Δ) :
    ∃ input : Protocol.NamedStore V, Proofs.NamedStore.Coherent S.E S.cfg input ∧ Data td input ∧
      S.hc.round_of input.core.s = a.round ∧
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
        hd, hround.symm, ?_⟩
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
        (data_at_event S rho sch he reader).1, delivery_round S rho sch a.round he hlo hhi, ?_⟩
      intro b hb
      rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he]
      exact hb
  · have hbefore : Proofs.NamedStore.Coherent S.E S.cfg before ∧ Data td before ∧
        S.hc.round_of before.core.s = a.round := by
      rcases hF1.1 with ⟨t, he, rfl⟩ | ⟨t, he, hem, rfl⟩
      · have ht : t = td := handle_event_time S rho hcall he
        subst t
        exact ⟨(Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          (data_at_event S rho sch he reader).1, delivery_round S rho sch a.round he hlo hhi⟩
      · have ht : t = td := handle_event_time S rho hcall he
        subst t
        refine ⟨NamedStore.coherent_clock S.E S.cfg _ td
          (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1,
          clock_data S td _ td le_rfl (data_at_event S rho sch he reader).1, ?_⟩
        change S.hc.round_of (S.E.slotOf td) = a.round
        rw [Proofs.HealingLemmas.slotOf_of_between_a S a.round hlo hhi,
          Proofs.HealingLemmas.round_of_opening_succ]
    let input := Execution.NamedReceiptCalls.f1Input S before B k
    have hcore := NamedStore.coherent_process_block S.E S.hc S.cfg before B hbefore.1
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg input :=
      NamedAdmission.coherent_admit_rows S.E S.hc S.cfg _ (B.attestations.take k) hcore
    have hd : Data td input := rows_data S td _ (B.attestations.take k) hcore
      (core_block_data S td before B hbefore.2.1)
    have hround : S.hc.round_of input.core.s = a.round := by
      rw [(NamedReceiptCallsF1.actual_f1_clock S rho i reader B k a before hF1).2]
      exact hbefore.2.2
    refine ⟨input, hcoh, hd, hround, ?_⟩
    intro b hb
    apply block_call_rows_after_event S rho hF1.1 b
    rw [(NamedReceiptCallsF1.actual_carried_call S rho i reader B k a before hF1).2.2.2.2]
    exact NamedReceiptCallsF1.admit_rows_mem_mono S.hc _ (B.attestations.drop (k + 1)) b hb

theorem pool_full_witness (S : Setup V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) (k : Round) (b : CombinedAttestation V)
    (hb : b ∈ st.core.sg_pool k) :
    ∃ named : NamedAttestation V, named ∈ st.sg_rows k ∧ named.erase = b := by
  change b ∈ (st.core.sg_votes k).toFinset at hb
  rw [hcoh.2.2.2.1 k] at hb
  exact List.mem_map.mp (List.mem_toFinset.mp hb)

/-- Identification uses the original held full row, authenticated at an
actual event prefix, then honest same-round uniqueness. Erasure/projection
equality alone is not used as full-row injectivity. -/
theorem honest_input_pool_row (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    {a : NamedAttestation V} (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (i : Nat) (reader : V) (input : Protocol.NamedStore V) (bound : Time)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg input) (hd : Data bound input)
    (hpost : ∀ b : NamedAttestation V,
      b ∈ (Protocol.NamedAdmission.admit_row S.hc input a).sg_rows b.round →
      b ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows b.round)
    (b : CombinedAttestation V) (hb : b ∈ input.core.sg_pool a.round)
    (hv : b.val_index = a.val_index) : b = a.erase ∧ a ∈ input.sg_rows a.round := by
  obtain ⟨named, hn, he⟩ := pool_full_witness S input hcoh a.round b hb
  have hr : named.round = a.round := (hd.2 a.round named hn).1
  have hown : named ∈ input.sg_rows named.round := by simpa only [hr] using hn
  have hheld := hpost named (NamedReceiptCallsF1.admit_row_mem_mono S.hc input a named hown)
  have hval : named.val_index = a.val_index := (congrArg CombinedAttestation.val_index he).trans hv
  have hhon : named.val_index ∈ rho.honest := by simpa only [hval] using ha
  obtain ⟨_, _, _, _, _, hnEmit⟩ :=
    NamedOutageProvenance.honest_held_row_emission S rho auth (i + 1) reader hheld hhon
  have hnEmit' : NamedRun.emits S rho a.val_index (.attest named) (S.a named.round) := by
    simpa only [hval] using hnEmit
  have hna : named = a := NamedOutageProvenance.emitted_same_round_unique S rho sch hnEmit' hem hr
  exact ⟨he.symm.trans (congrArg NamedAttestation.erase hna), by simpa only [hna] using hn⟩

theorem honest_row_after_call (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    {i : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (hcall : NamedRun.actualHandlesAt S rho i reader (.attest a) td)
    (hlo : S.a a.round ≤ td) (hhi : td < S.a a.round + S.E.Δ) :
    a ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.sg_rows a.round := by
  obtain ⟨input, hcoh, hd, hround, hpost⟩ := actual_call_input S rho sch hcall hlo hhi
  have hpool := honest_input_pool_row S rho sch auth ha hem i reader input td hcoh hd hpost
  have hsub : Protocol.round_votes input.core a.erase ⊆ {a.confirmed} := by
    intro key hk
    obtain ⟨b, hb, hv, hkey⟩ := Proofs.Optimistic.mem_round_votes.mp hk
    have he := (hpool b hb hv).1
    subst b
    exact Finset.mem_singleton.mpr hkey.symm
  by_cases hduplicate : a.confirmed ∈ Protocol.round_votes input.core a.erase
  · obtain ⟨b, hb, hv, _⟩ := Proofs.Optimistic.mem_round_votes.mp hduplicate
    have hheld := (hpool b hb hv).2
    exact hpost a (NamedReceiptCallsF1.admit_row_mem_mono S.hc input a a hheld)
  · have hcard : (Protocol.round_votes input.core a.erase).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsub
    have hguard : ¬ (a.round < S.hc.round_of input.core.s - S.hc.η_SG ∨
        S.hc.round_of input.core.s < a.round ∨
        a.confirmed ∈ Protocol.round_votes input.core a.erase ∨
        (Protocol.round_votes input.core a.erase).card = 2) := by
      rw [hround]
      simp only [not_or]
      exact ⟨Nat.not_lt.mpr (Nat.sub_le _ _), Nat.lt_irrefl _, hduplicate, by omega⟩
    have hpre : a.erase ∉ input.core.sg_pool a.round := by
      intro hmem
      exact hduplicate (Proofs.Optimistic.mem_round_votes.mpr ⟨a.erase, hmem, rfl, rfl⟩)
    have hnew : a.erase ∈ (Protocol.on_sg_vote S.hc input.core a.erase).sg_pool a.round := by
      dsimp only [Protocol.on_sg_vote]
      simp only [show a.erase.round = a.round from rfl,
        show a.erase.confirmed = a.confirmed from rfl]
      rw [if_neg hguard]
      simp [Protocol.Store.sg_pool]
    exact hpost a (NamedAdmission.admitted_original_row S.hc input a hpre hnew)


theorem early_le_domain (S : Setup V) (q : Round) :
    DecoupledConsensusModel.Protocol.early S.E S.hc q .g2 ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 := by
  change DecoupledConsensusModel.Protocol.opening S.E S.hc q + (-5) * S.E.Δ ≤
    DecoupledConsensusModel.Protocol.opening S.E S.hc q + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (show (-5 : Time) ≤ -1 by decide) S.E.Δ_pos.le) _

theorem previous_round_in_window (S : Setup V) (q : Round) :
    q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
  simpa only [Nat.add_sub_cancel] using
    Protocol.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)







end DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival

end
