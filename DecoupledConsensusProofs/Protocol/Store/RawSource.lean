module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.PublicCutSG
public import DecoupledConsensusProofs.Protocol.Schedule.ReceiptCallsF1

@[expose] public section

/-! Source raw-view to original full acceptance composition.
The source SG sender can be faulty. No grade or body-open conclusion. -/
namespace DecoupledConsensusModel.Proofs.NamedRawSource
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private def RowsOwn (st : Protocol.NamedStore V) : Prop :=
  ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k → a.round = k

omit [Fintype V] in
private theorem row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

omit [Fintype V] in
private theorem row_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming : NamedAttestation V) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.admit_row hc st incoming) := by
  intro k a ha
  rcases row_mem_cases_at hc st incoming a k ha with hold | ⟨rfl, rfl⟩
  · exact h k a hold
  · rfl

omit [Fintype V] in
private theorem rows_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_own hc st a h)

private theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

private theorem block_own (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hc : RowsOwn (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) := by
    simpa only [RowsOwn, core_block_rows] using h
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_own S.hc _ B.attestations hc
  · exact hc

private theorem propose_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_own S st _ h

private theorem tick_preserves_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (t : Time) (P : Protocol.NamedStore V → Prop)
    (hclock : ∀ st, P st → P (Protocol.NamedStore.setClock S.E st t))
    (hprop : ∀ st, P st →
      P (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1)
    (hgf : ∀ st, P st →
      P (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1)
    (hconf : ∀ st s, P st →
      P (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s))
    (hatt : ∀ st record, P st →
      P (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (h : P st) :
    P (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> solve_by_elim (maxDepth := 10) [hclock, hprop, hgf, hconf, hatt]

private theorem tick_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  have hclock : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedStore.setClock S.E st t) := fun _ hs => hs
  have hprop : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 :=
    propose_own gc S nd
  have hgf : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := fun _ hs => hs
  have hconf : ∀ st s, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) := fun _ _ hs => hs
  have hatt : ∀ st record, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
    fun st record hs => row_own S.hc st _ hs
  exact tick_preserves_own gc S nd t RowsOwn hclock hprop hgf hconf hatt st record h

private theorem process_own (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V)
    (h : RowsOwn st) : RowsOwn (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_own S st B h
  | gfVote u => exact h
  | attest a => exact row_own S.hc st a h

private theorem own_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (reader : V) :
    RowsOwn (NamedRun.stateBefore S rho i reader).st := by
  induction i with
  | zero =>
    intro k a ha
    simp only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, List.not_mem_nil] at ha
  | succ i ih =>
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => exact ih
    | some e =>
      change RowsOwn (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
      by_cases hv : reader = e.node
      · cases e with
        | tick v t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_tick]
          exact tick_own _ S (S.node reader) _ _ t ih
        | deliver v o t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_deliver]
          exact process_own S _ o ih
      · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
        exact ih

private theorem own_strict_read (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (read : Time) (reader : V) :
    RowsOwn (NamedRun.stateBeforeTime S rho read reader).st := by
  obtain ⟨n, hn, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  rw [hn]
  exact own_stateBefore S rho n reader


/-- **Public twin of the `RowsOwn` fold**: a full named row
held in bucket `k` of any prefix state is a round-`k` row. The fold itself is
the private induction above; only this reading is exported. -/
theorem row_round_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (reader : V)
    (k : Round) (a : NamedAttestation V)
    (ha : a ∈ (NamedRun.stateBefore S rho i reader).st.sg_rows k) : a.round = k :=
  own_stateBefore S rho i reader k a ha

/-- The strict-read twin of `row_round_stateBefore`. -/
theorem row_round_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (read : Time) (reader : V)
    (k : Round) (a : NamedAttestation V)
    (ha : a ∈ (NamedRun.stateBeforeTime S rho read reader).st.sg_rows k) : a.round = k :=
  own_strict_read S rho sch read reader k a ha

private theorem window_bounds {eta s k : Round} (hk : k ∈ Protocol.latest_window eta s) :
    s - eta ≤ k ∧ k < s := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  refine ⟨Nat.le_add_right _ _, ?_⟩
  by_cases heta : eta ≤ s
  · have hsum : s - eta + eta = s := Nat.sub_add_cancel heta
    have hiEta : i < eta := by simpa only [Nat.min_eq_right heta] using hi
    calc
      s - eta + i < s - eta + eta := Nat.add_lt_add_left hiEta _
      _ = s := hsum
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge heta), Nat.zero_add]
    exact hi.trans_le (Nat.min_le_left s eta)

private theorem early_g2_public (S : Setup V) (s : Round) (hs : 0 < s) :
    PublicTime S (early S.E S.hc s .g2) := by
  have hslots : 2 ≤ s * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hs)
  have hcoef : 5 ≤ 4 * (s * S.hc.R) := by
    calc
      5 ≤ 4 * 2 := by decide
      _ ≤ 4 * (s * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (s * S.hc.R) - 5, ?_⟩
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

/-- Recover the retained original full row without treating SG projection
equality as full identity. The public early cutoff supplies actual timing. -/
theorem g2_raw_input_source_acceptance
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    (source : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g2) source).st.core.toHealing.gradeView
      S.hc.η_SG s (early S.E S.hc s .g2) sender) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      Protocol.sgVote a.erase = u ∧ a.round ∈ Protocol.latest_window S.hc.η_SG s ∧
      accepted < early S.E S.hc s .g2 ∧
      NamedRun.acceptsAt S rho i source (.attest a) accepted := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g2) source
  obtain ⟨hpool, _, hstamp⟩ := Finset.mem_filter.mp hraw
  obtain ⟨k, hk, hu⟩ := Finset.mem_biUnion.mp hpool
  have hwindow : k ∈ Protocol.latest_window S.hc.η_SG s := List.mem_toFinset.mp hk
  have hs : 0 < s := (Nat.zero_le k).trans_lt (window_bounds hwindow).2
  change u ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc s .g2) source).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := own_strict_read S rho sch (domain S.E S.hc s .g2) source k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : Protocol.sgVote a.erase = u := (congrArg Protocol.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc s .g2) = true := by
    rw [hprojection]
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch
      (early_g2_public S s hs) hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

private theorem early_g1_public (S : Setup V) (s : Round) (hs : 0 < s) :
    PublicTime S (early S.E S.hc s .g1) := by
  have hslots : 2 ≤ s * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hs)
  have hcoef : 4 ≤ 4 * (s * S.hc.R) := by
    calc
      4 ≤ 4 * 2 := by decide
      _ ≤ 4 * (s * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (s * S.hc.R) - 4, ?_⟩
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

/-- G1/G0 twin of `g2_raw_input_source_acceptance`: recover the retained
original full row from a raw G1-early source token. The public early cutoff
supplies actual timing. Its proof calls the same file-private
`own_strict_read`/`window_bounds` at the `.g1` cutoff, phase-shifted from the
`.g2` original with no other change. -/
theorem g1_raw_input_source_acceptance
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    (source : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) source).st.core.toHealing.gradeView
      S.hc.η_SG s (early S.E S.hc s .g1) sender) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      Protocol.sgVote a.erase = u ∧ a.round ∈ Protocol.latest_window S.hc.η_SG s ∧
      accepted < early S.E S.hc s .g1 ∧
      NamedRun.acceptsAt S rho i source (.attest a) accepted := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) source
  obtain ⟨hpool, _, hstamp⟩ := Finset.mem_filter.mp hraw
  obtain ⟨k, hk, hu⟩ := Finset.mem_biUnion.mp hpool
  have hwindow : k ∈ Protocol.latest_window S.hc.η_SG s := List.mem_toFinset.mp hk
  have hs : 0 < s := (Nat.zero_le k).trans_lt (window_bounds hwindow).2
  change u ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc s .g1) source).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := own_strict_read S rho sch (domain S.E S.hc s .g1) source k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : Protocol.sgVote a.erase = u := (congrArg Protocol.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc s .g1) = true := by
    rw [hprojection]
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch
      (early_g1_public S s hs) hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

private theorem late_g1_public (S : Setup V) (s : Round) (hs : 0 < s) :
    PublicTime S (late S.E S.hc s .g1) := by
  have hslots : 2 ≤ s * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hs)
  have hcoef : 2 ≤ 4 * (s * S.hc.R) := by
    calc
      2 ≤ 4 * 2 := by decide
      _ ≤ 4 * (s * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (s * S.hc.R) - 2, ?_⟩
  unfold late opening Phase.lateOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

/-- A raw G1-late input has an original full named representative accepted
strictly before the G1 late cutoff. The SG sender may be faulty. -/
theorem g1_late_raw_input_acceptance
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    (reader : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) reader).st.core.toHealing.gradeView
      S.hc.η_SG s (late S.E S.hc s .g1) sender) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      Protocol.sgVote a.erase = u ∧ a.round ∈ Protocol.latest_window S.hc.η_SG s ∧
      accepted < late S.E S.hc s .g1 ∧
      NamedRun.acceptsAt S rho i reader (.attest a) accepted := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) reader
  obtain ⟨hpool, _, hstamp⟩ := Finset.mem_filter.mp hraw
  obtain ⟨k, hk, hu⟩ := Finset.mem_biUnion.mp hpool
  have hwindow : k ∈ Protocol.latest_window S.hc.η_SG s := List.mem_toFinset.mp hk
  have hs : 0 < s := (Nat.zero_le k).trans_lt (window_bounds hwindow).2
  change u ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc s .g1) reader).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := own_strict_read S rho sch (domain S.E S.hc s .g1) reader k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : Protocol.sgVote a.erase = u := (congrArg Protocol.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (late S.E S.hc s .g1) = true := by
    rw [hprojection]
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch
      (late_g1_public S s hs) hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

private theorem late_g0_public (S : Setup V) (s : Round) (hs : 0 < s) :
    PublicTime S (late S.E S.hc s .g0) := by
  have hslots : 2 ≤ s * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hs)
  have hcoef : 3 ≤ 4 * (s * S.hc.R) := by
    calc
      3 ≤ 4 * 2 := by decide
      _ ≤ 4 * (s * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (s * S.hc.R) - 3, ?_⟩
  unfold late opening Phase.lateOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring


/-- G0/G1 twin of `g1_late_raw_input_acceptance`. This instance is not one of
the four originally-flagged missing lemmas: it is an additional reader-side
twin required by `NamedReverseRawSource.g0_late_raw_input_reverse_at_g1_late`
(item 4), which composes it with the item-3 relay instance exactly as the
template composes `g1_late_raw_input_acceptance` with the `.g2`-late relay. -/
theorem g0_late_raw_input_acceptance
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    (reader : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g0) reader).st.core.toHealing.gradeView
      S.hc.η_SG s (late S.E S.hc s .g0) sender) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      Protocol.sgVote a.erase = u ∧ a.round ∈ Protocol.latest_window S.hc.η_SG s ∧
      accepted < late S.E S.hc s .g0 ∧
      NamedRun.acceptsAt S rho i reader (.attest a) accepted := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g0) reader
  obtain ⟨hpool, _, hstamp⟩ := Finset.mem_filter.mp hraw
  obtain ⟨k, hk, hu⟩ := Finset.mem_biUnion.mp hpool
  have hwindow : k ∈ Protocol.latest_window S.hc.η_SG s := List.mem_toFinset.mp hk
  have hs : 0 < s := (Nat.zero_le k).trans_lt (window_bounds hwindow).2
  change u ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc s .g0) reader).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := own_strict_read S rho sch (domain S.E S.hc s .g0) reader k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : Protocol.sgVote a.erase = u := (congrArg Protocol.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (late S.E S.hc s .g0) = true := by
    rw [hprojection]
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch
      (late_g0_public S s hs) hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

end DecoupledConsensusModel.Proofs.NamedRawSource

end
