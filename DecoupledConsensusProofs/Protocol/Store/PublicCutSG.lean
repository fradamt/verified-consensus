module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Schedule.ReceiptCallsF1

@[expose] public section

/-! SG public-cut converse, including faulty senders.
The full event's first insertion is used, not a selected duplicate F1 call.
-/
namespace DecoupledConsensusModel.Proofs.NamedPublicCutSG
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem rows_split_at (rows : List (NamedAttestation V)) (j : Nat)
    (a : NamedAttestation V) (h : rows[j]? = some a) :
    rows = rows.take j ++ a :: rows.drop (j + 1) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j rows]
  rw [List.drop_eq_getElem_cons hj, hget]

set_option linter.unusedFintypeInType false in
/-- The first changing call can differ from the actualHandlesAt F1 witness. -/
private theorem rows_new_stamp (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_rows hc st rows).sg_rows a.round) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (st.core.t : Stamp) := by
  obtain ⟨j, _, hrow, hbefore, hafter⟩ :=
    NamedReceiptCallsF1.admit_rows_new_marker hc st rows a hpre hpost
  have hsplit := rows_split_at rows j a hrow
  have hdecomp : Protocol.NamedAdmission.admit_rows hc st rows =
      Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc
          (Protocol.NamedAdmission.admit_rows hc st (rows.take j)) a)
        (rows.drop (j + 1)) := by
    conv_lhs => rw [hsplit]
    simp only [Protocol.NamedAdmission.admit_rows, List.foldl_append, List.foldl_cons]
  rw [hdecomp, NamedReceiptCallsF1.full_new_row_stamp_after_suffix hc _ a _ hbefore hafter,
    (NamedAdmission.admit_rows_clock hc st (rows.take j)).1]

private theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

private theorem block_new_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (st.core.t : Stamp) := by
  have hpreCore : a ∉
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows a.round := by
    simpa only [core_block_rows] using hpre
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost ⊢
  split_ifs at hpost ⊢
  · rw [rows_new_stamp S.hc _ B.attestations a hpreCore hpost,
      (NamedAdmission.process_block_clock S.E S.hc S.cfg st B).1]
  · exact False.elim (hpreCore hpost)

private theorem propose_new_stamp (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.sg_rows a.round) :
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (st.core.t : Stamp) := by
  unfold Protocol.NamedDuties.propose_block_with at hpost ⊢
  cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried
      S.E S.hc nd st with
  | none =>
    simp only [hp] at hpost ⊢
    exact False.elim (hpre hpost)
  | some B =>
    simp only [hp] at hpost ⊢
    exact block_new_stamp S st B a hpre hpost

private theorem propose_coherent (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Proofs.NamedStore.Coherent S.E S.cfg
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact NamedAdmission.coherent_on_block .alsoCarried S.E S.hc S.cfg st _ h

private theorem propose_clock (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core.t = st.core.t := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · rfl
  · exact (NamedAdmission.on_block_clock .alsoCarried S.E S.hc S.cfg st _).1

private theorem gf_checked_stamp (E : Env V) (st : Protocol.Store V) (a : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st a).timestamp_sg_vote = st.timestamp_sg_vote := by
  unfold Protocol.on_goldfish_vote_checked Protocol.on_goldfish_vote
  split_ifs <;> rfl

private theorem gf_stamp (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core.timestamp_sg_vote =
      st.core.timestamp_sg_vote := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_checked_stamp S.E _ _
  · rfl

private theorem gf_clock (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core.t = st.core.t := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_time S.E _ _
  · rfl



private theorem confirmation_stamp (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core.timestamp_sg_vote =
      st.core.timestamp_sg_vote := rfl

private theorem confirmation_clock (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core.t = st.core.t := rfl

/-- Every row first introduced by this whole tick has its tick-time stamp,
whether its first call is in the proposal's F1 list or the own-row duty. -/
private theorem tick_new_stamp (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.sg_rows a.round) :
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (t : Stamp) := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let due := 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index
  let st1 := if due then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hc0 : Proofs.NamedStore.Coherent S.E S.cfg st0 := NamedStore.coherent_clock S.E S.cfg st t hcoh
  have hc1 : Proofs.NamedStore.Coherent S.E S.cfg st1 := by
    dsimp only [st1]; split_ifs
    · exact propose_coherent gc S nd st0 hc0
    · exact hc0
  have hc2 : Proofs.NamedStore.Coherent S.E S.cfg st2 := by
    dsimp only [st2]; split_ifs
    · exact NamedDuties.coherent_goldfish_vote gc S.E S.hc S.cfg nd st1 hc1
    · exact hc1
  have hc3 : Proofs.NamedStore.Coherent S.E S.cfg st3 := by
    dsimp only [st3]; split_ifs
    · exact NamedDuties.coherent_confirmation gc S.E S.hc S.cfg st2 (s - 1) hc2
    · exact hc2
  have hrows31 : st3.sg_rows = st1.sg_rows := by dsimp only [st3, st2]; split_ifs <;> rfl
  have hstamp31 : st3.core.timestamp_sg_vote = st1.core.timestamp_sg_vote := by
    dsimp only [st3, st2]
    split_ifs <;> simp only [confirmation_stamp, gf_stamp]
  have hclock3 : st3.core.t = t := by
    dsimp only [st3, st2, st1]
    split_ifs <;>
      simp only [confirmation_clock, gf_clock, propose_clock, st0, Protocol.NamedStore.setClock]
  have hnew3 : a ∈ st3.sg_rows a.round →
      st3.core.timestamp_sg_vote (Protocol.sgVote a.erase) = some (t : Stamp) := by
    intro ha3
    rw [hrows31] at ha3
    rw [hstamp31]
    by_cases hdue : due
    · have hap : a ∈
          (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1.sg_rows a.round := by
        simpa only [st1, if_pos hdue] using ha3
      simpa only [st1, if_pos hdue] using propose_new_stamp gc S nd st0 a hpre hap
    · exact False.elim (hpre (by simpa only [st1, if_neg hdue] using ha3))
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true
        then (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, due, s]
    split_ifs <;> rfl
  rw [hstore] at hpost ⊢
  split_ifs at hpost ⊢
  · let incoming := (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).2.2
    change a ∈ (Protocol.NamedAdmission.admit_row S.hc st3 incoming).sg_rows a.round at hpost
    change (Protocol.NamedAdmission.admit_row S.hc st3 incoming).core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (t : Stamp)
    by_cases hold : a ∈ st3.sg_rows a.round
    · exact
        (NamedAdmission.existing_row_stamp S.hc st3 hc3.2.2.2.1 incoming a hold).trans
          (hnew3 hold)
    · have heq : a = incoming :=
        (NamedReceiptCallsF1.admit_row_mem_cases S.hc st3 incoming a hpost).resolve_left hold
      rw [← heq] at hpost ⊢
      rw [NamedReceiptCallsF1.full_new_row_stamp S.hc st3 a hold hpost, hclock3]
  · exact hnew3 hpost

private theorem process_new_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (o : NamedObject V) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (NamedReceipt.process S st o).sg_rows a.round) :
    (NamedReceipt.process S st o).core.timestamp_sg_vote (Protocol.sgVote a.erase) =
      some (st.core.t : Stamp) := by
  cases o with
  | block B => exact block_new_stamp S st B a hpre hpost
  | gfVote u => exact False.elim (hpre hpost)
  | attest incoming =>
    have heq : a = incoming :=
      (NamedReceiptCallsF1.admit_row_mem_cases S.hc st incoming a hpost).resolve_left hpre
    subst incoming
    exact NamedReceiptCallsF1.full_new_row_stamp S.hc st a hpre hpost

private theorem accepted_row_stamp_cases (S : Setup V) (rho : NamedRun V)
    {j : Nat} {reader : V} {a : NamedAttestation V} {accepted : Time}
    (hacc : NamedRun.acceptsAt S rho j reader (.attest a) accepted) :
    (∃ _htick : rho.events[j]? = some (.tick reader accepted),
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase) = some (accepted : Stamp)) ∨
    (∃ o : NamedObject V, ∃ _hdeliver : rho.events[j]? = some (.deliver reader o accepted),
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase) =
          some ((NamedRun.stateBefore S rho j reader).st.core.t : Stamp)) := by
  have hpre : a ∉ (NamedRun.stateBefore S rho j reader).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hacc.2.1
  have hpost : a ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | tick v t =>
    change v = reader at hnode
    change t = accepted at htime
    subst v
    subst t
    refine Or.inl ⟨he, ?_⟩
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he] at hpost ⊢
    exact tick_new_stamp _ S (S.node reader) _ _ accepted a
      (Proofs.NamedRuntime.stateBefore_invariants S rho j reader).1.1.1 hpre hpost
  | deliver v o t =>
    change v = reader at hnode
    change t = accepted at htime
    subst v
    subst t
    refine Or.inr ⟨o, he, ?_⟩
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho he] at hpost ⊢
    exact process_new_stamp S _ o a hpre hpost

private theorem publicTime_nonneg (S : Setup V) {cut : Time}
    (hpublic : PublicTime S cut) : 0 ≤ cut := by
  obtain ⟨k, rfl⟩ := hpublic
  exact Int.mul_nonneg (by exact_mod_cast Nat.zero_le k) S.E.Δ_pos.le


omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le


private theorem tick_index_le_target_event (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {k j : Nat} {reader : V}
    {cut : Time} {e : NamedEvent V}
    (htick : rho.events[k]? = some (.tick reader cut))
    (he : rho.events[j]? = some e) (hnode : e.node = reader)
    (hcut : cut ≤ e.time) : k ≤ j := by
  by_contra hnot
  have hjk : j < k := Nat.lt_of_not_ge hnot
  obtain ⟨hk, hgetk⟩ := List.getElem?_eq_some_iff.mp htick
  obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp he
  have hkey := (List.pairwise_iff_getElem.mp sch.sorted) j k hj hk hjk
  rw [hgetj, hgetk] at hkey
  have htime : e.time ≤ cut := time_le_of_key_le hkey
  have heqtime : e.time = cut := le_antisymm htime hcut
  cases e with
  | deliver v o eventTime =>
      simp only [NamedEvent.node] at hnode
      simp only [NamedEvent.time] at heqtime
      subst v
      subst eventTime
      simp only [NamedEvent.key, NamedEvent.time, NamedEvent.phase,
        Prod.Lex.le_iff] at hkey
      rcases hkey with hlt | ⟨_, hphase⟩
      · exact (lt_irrefl cut) hlt
      · norm_num at hphase
  | tick v eventTime =>
      simp only [NamedEvent.node] at hnode
      simp only [NamedEvent.time] at heqtime
      subst v
      subst eventTime
      have hev : rho.events[j] = rho.events[k] := by
        rw [hgetj, hgetk]
      have hjkeq : j = k := (List.Nodup.getElem_inj_iff sch.nodup).mp hev
      exact (ne_of_lt hjk) hjkeq

/-- Any full row whose retained SG projection stamp precedes a public cut
has an original full-row acceptance before that cut. The sender may be faulty.
There is no ordering premise on the observation read and the public cut. -/
theorem sg_row_accepted_before_public_cut
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {reader : V} {cut read : Time} (hpublic : PublicTime S cut) {a : NamedAttestation V}
    (hheld : a ∈ (NamedRun.stateBeforeTime S rho read reader).st.sg_rows a.round)
    (hstamp : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho read reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase))
      cut = true) :
    ∃ (j : Nat) (accepted : Time), accepted < cut ∧
      NamedRun.acceptsAt S rho j reader (.attest a) accepted := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  rw [hread] at hheld hstamp
  obtain ⟨j, hj, accepted, hacc⟩ := NamedOutageProvenance.held_row_origin S rho n reader hheld
  by_cases hearly : accepted < cut
  · exact ⟨j, accepted, hearly, hacc⟩
  · have hcutAccepted : cut ≤ accepted := le_of_not_gt hearly
    have hpost : a ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows a.round := by
      simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
    have htransport := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono
      S rho reader (Nat.succ_le_of_lt hj) hpost
    have hstampPost : occurrenceBefore
        ((NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase))
        cut = true := by
      rw [← htransport.2]
      exact hstamp
    obtain ⟨e, he, hnode, het⟩ := hacc.1.2
    have hreader : reader ∈ rho.honest := by
      simpa only [hnode] using sch.honest_only e (List.mem_of_getElem? he)
    have hacceptedHorizon : accepted ≤ rho.horizon := by
      simpa only [het] using (sch.in_horizon e (List.mem_of_getElem? he)).2
    have htickMem := sch.tick_total reader hreader cut hpublic
      (publicTime_nonneg S hpublic) (hcutAccepted.trans hacceptedHorizon)
    obtain ⟨k, htick⟩ := List.mem_iff_getElem?.mp htickMem
    have hkj := tick_index_le_target_event rho sch htick he hnode
      (by simpa only [het] using hcutAccepted)
    rcases accepted_row_stamp_cases S rho hacc with
      ⟨_, hpostStamp⟩ | ⟨o, hdeliver, hpostStamp⟩
    · rw [hpostStamp] at hstampPost
      simp only [occurrenceBefore, decide_eq_true_eq] at hstampPost
      exact False.elim ((not_lt_of_ge (by exact_mod_cast hcutAccepted)) hstampPost)
    · have hkne : k ≠ j := by
        intro hEq
        subst k
        rw [htick] at hdeliver
        cases hdeliver
      have hclock := Proofs.NamedRuntime.tick_time_le_clock S rho sch.sorted
        (fun event hmem => (sch.in_horizon event hmem).1) htick (lt_of_le_of_ne hkj hkne)
      rw [hpostStamp] at hstampPost
      simp only [occurrenceBefore, decide_eq_true_eq] at hstampPost
      have hclockStamp : (cut : Stamp) ≤
          ((NamedRun.stateBefore S rho j reader).st.core.t : Stamp) := by exact_mod_cast hclock
      exact False.elim ((not_lt_of_ge hclockStamp) hstampPost)

end DecoupledConsensusModel.Proofs.NamedPublicCutSG

end
