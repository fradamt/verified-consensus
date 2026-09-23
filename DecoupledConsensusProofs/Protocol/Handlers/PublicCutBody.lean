module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp

@[expose] public section

/-!
Compiler-free draft for the public-cut converse. The imported module name is
the proposed active destination of the separately frozen block-stamp records.
All support facts below are private; the last theorem is the only public query.
-/


namespace DecoupledConsensusModel.Proofs.NamedPublicCutBody
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

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

omit [DecidableEq V] [Fintype V] in
private theorem index_lt_of_time_lt (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i j : Nat} {e f : NamedEvent V}
    (he : rho.events[i]? = some e) (hf : rho.events[j]? = some f)
    (ht : e.time < f.time) : i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases hji.eq_or_lt with rfl | hji
  · have hef : e = f := Option.some.inj (he.symm.trans hf)
    exact (ne_of_lt ht) (congrArg NamedEvent.time hef)
  · obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hf
    have hkey := (List.pairwise_iff_getElem.mp hsorted) j i hj hi hji
    rw [hgetj, hgeti] at hkey
    exact (not_lt_of_ge (time_le_of_key_le hkey)) ht

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

private theorem stateBeforeTime_eq_full_of_horizon_lt (S : Setup V)
    (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {cut : Time} (hhorizon : rho.horizon < cut) :
    NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho rho.events.length := by
  unfold NamedRun.stateBeforeTime NamedRun.stateBefore
  rw [List.filter_eq_self.mpr, List.take_length]
  intro e he
  simp only [decide_eq_true_eq]
  exact (sch.in_horizon e he).2.trans_lt hhorizon

private theorem accepted_earlier_held_at_cut (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {reader : V} {cut : Time}
    (hpublic : PublicTime S cut) {j : Nat} {e : NamedEvent V}
    (he : rho.events[j]? = some e) (hnode : e.node = reader)
    (hearly : e.time < cut) {B : NamedBlock V}
    (hpost : B ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies) :
    B ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  by_cases hhor : cut ≤ rho.horizon
  · have hreader : reader ∈ rho.honest :=
      by simpa only [hnode] using
        sch.honest_only e (List.mem_of_getElem? he)
    have htickMem := sch.tick_total reader hreader cut hpublic
      (publicTime_nonneg S hpublic) hhor
    obtain ⟨k, htick⟩ := List.mem_iff_getElem?.mp htickMem
    have hjk := index_lt_of_time_lt rho sch.sorted he htick hearly
    rw [← Proofs.NamedRuntime.tick_prefix_eq_strict S rho sch.sorted sch.nodup htick]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho reader
      (Nat.succ_le_of_lt hjk) hpost
  · have hhorizon : rho.horizon < cut := lt_of_not_ge hhor
    rw [stateBeforeTime_eq_full_of_horizon_lt S rho sch hhorizon]
    obtain ⟨hjlen, _⟩ := List.getElem?_eq_some_iff.mp he
    exact NamedBodyRetention.stateBefore_bodies_mono S rho reader
      (Nat.succ_le_of_lt hjlen) hpost

omit [Fintype V] in
private theorem rows_block_stamp (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.timestamp_block =
      st.core.timestamp_block := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rows).core.timestamp_block = _
    rw [ih]
    exact (NamedAdmission.admit_row_fixed_fields hc st row).2.2.2.1

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
    rw [ih, NamedAdmission.admit_row_bodies]

private theorem checked_new_block_stamp (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (hpre : B ∉ st.T)
    (hpost : B ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState)
      hc st B).timestamp_block B = some (st.t : Stamp) := by
  dsimp only [Protocol.on_block_checked_using] at hpost ⊢
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · simp only [hvalid, if_true] at hpost ⊢
    by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · simp only [Protocol.on_block_using, if_pos hfirst] at hpost
      exact False.elim (hpre hpost)
    · by_cases hfinal : (!Block.preceq st.F B) = true
      · simp only [Protocol.on_block_using, if_neg hfirst, if_pos hfinal] at hpost
        exact False.elim (hpre hpost)
      · by_cases hproposer : B.proposer? ≠ some (E.proposer B.slot)
        · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
            if_pos hproposer] at hpost
          exact False.elim (hpre hpost)
        · by_cases hparent : ¬ B.parent.slot < B.slot
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_pos hparent] at hpost
            exact False.elim (hpre hpost)
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_neg hparent,
              Protocol.update_finality_timestamp_block,
              Protocol.foldl_on_goldfish_vote_checked_timestamp_block]
            simp
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp only [hfalse, Bool.false_eq_true, if_false] at hpost
    exact False.elim (hpre hpost)

private theorem core_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_block B.erase =
      some (st.core.t : Stamp) := by
  unfold Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost
    exact False.elim (hpre hpost)
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies at hpost
    change (Protocol.NamedStore.commitBlock st after B).core.timestamp_block B.erase = _
    by_cases hfresh : B.erase ∉ st.core.T ∧ B.erase ∈ after.T
    · unfold Protocol.NamedStore.commitBlock
      rw [if_pos hfresh]
      exact checked_new_block_stamp S.E S.hc st.core B.erase _ hfresh.1 hfresh.2
    · unfold Protocol.NamedStore.commitBlock at hpost ⊢
      rw [if_neg hfresh] at hpost
      exact False.elim (hpre hpost)

private theorem block_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedAdmission.on_block_with
      .alsoCarried S.E S.hc S.cfg st B).core.timestamp_block B.erase =
        some (st.core.t : Stamp) := by
  let core := Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B
  have hcore : B ∈ core.bodies := by
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost
    split_ifs at hpost
    · simpa only [rows_bodies] using hpost
    · exact hpost
  have hs := core_new_body_stamp S st B hpre hcore
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · simpa only [rows_block_stamp] using hs
  · exact hs

private theorem emitted_block_due (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (B : NamedBlock V)
    (hB : NamedObject.block B ∈
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2) :
    0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index := by
  by_contra hnot
  rw [NamedTick.tick_computed_duties] at hB
  dsimp only at hB
  simp only [if_neg hnot] at hB
  split_ifs at hB <;>
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, and_false, exists_false] at hB

private theorem tick_proposal_stage_fields (gc : Protocol.GradeContract V)
    (S : Setup V) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
        S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.bodies = st1.bodies ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.timestamp_block =
        st1.core.timestamp_block := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hb31 : st3.bodies = st1.bodies := by
    dsimp only [st3, st2]
    split_ifs <;> rfl
  have hs21 : st2.core.timestamp_block = st1.core.timestamp_block := by
    dsimp only [st2, Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    split_ifs <;> first
      | exact Protocol.on_goldfish_vote_checked_timestamp_block S.E _ _
      | rfl
  have hs31 : st3.core.timestamp_block = st1.core.timestamp_block := by
    dsimp only [st3]
    split_ifs <;> exact hs21
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact ⟨by
      simp only [Protocol.NamedDuties.attest_with, NamedAdmission.admit_row_bodies]
      exact hb31,
      (NamedAdmission.admit_row_fixed_fields S.hc st3 _).2.2.2.1.trans hs31⟩
  · exact ⟨hb31, hs31⟩

private theorem accepted_block_stamp_cases (S : Setup V) (rho : NamedRun V)
    {j : Nat} {reader : V} {B : NamedBlock V} {accepted : Time}
    (hacc : NamedRun.acceptsAt S rho j reader (.block B) accepted) :
    (∃ _htick : rho.events[j]? = some (.tick reader accepted),
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_block B.erase =
        some (accepted : Stamp)) ∨
    (∃ _hdeliver : rho.events[j]? = some (.deliver reader (.block B) accepted),
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_block B.erase =
        some ((NamedRun.stateBefore S rho j reader).st.core.t : Stamp)) := by
  have hpre : B ∉ (NamedRun.stateBefore S rho j reader).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hacc.2.1
  have hpost : B ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  rcases hacc.1.1 with ⟨eventTime, htick, hem⟩ | ⟨eventTime, hdeliver⟩
  · have htime : eventTime = accepted := by
      obtain ⟨e, he, _, het⟩ := hacc.1.2
      have heq : NamedEvent.tick reader eventTime = e :=
        Option.some.inj (htick.symm.trans he)
      simpa only [NamedEvent.time] using
        (congrArg NamedEvent.time heq).trans het
    subst eventTime
    left
    refine ⟨htick, ?_⟩
    have hcall := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hem
    let pre := NamedRun.stateBefore S rho j reader
    let c := DecoupledConsensusModel.Protocol.onPhaseTick
      S.E S.hc pre.st.core.toHealing accepted pre.cache
    let gc := DecoupledConsensusModel.Protocol.frameContract c
    let before := Protocol.NamedStore.setClock S.E pre.st accepted
    have hemTick := hem
    change NamedObject.block B ∈
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node reader)
        pre.st pre.record accepted).2.2 at hemTick
    have hdue := emitted_block_due gc S.E S.hc S.cfg (S.node reader)
      pre.st pre.record accepted B hemTick
    have hstage := tick_proposal_stage_fields gc S (S.node reader)
      pre.st pre.record accepted
    rw [Proofs.NamedRuntime.stateBefore_tick S rho htick] at hpost ⊢
    change B ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg
      (S.node reader) pre.st pre.record accepted).1.bodies at hpost
    change (Protocol.NamedTick.tick gc S.E S.hc S.cfg
      (S.node reader) pre.st pre.record accepted).1.core.timestamp_block B.erase = _
    have hpostProposal : B ∈
        (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
          (S.node reader) before).1.bodies := by
      rw [hstage.1] at hpost
      simpa only [if_pos hdue] using hpost
    have hcallStore :
        (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
          (S.node reader) before).1 =
        (Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B) := by
      exact congrArg Prod.fst hcall
    have hpostOn : B ∈ (Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B).bodies := by
      rw [← hcallStore]
      exact hpostProposal
    have hpreBefore : B ∉ before.bodies := by
      simpa only [before, Protocol.NamedStore.setClock] using hpre
    have hnew := block_new_body_stamp S before B hpreBefore hpostOn
    calc
      _ = (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
          (S.node reader) before).1.core.timestamp_block B.erase := by
            rw [hstage.2]
            simp only [if_pos hdue]
            rfl
      _ = (Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B).core.timestamp_block B.erase := by
            rw [hcallStore]
      _ = _ := by simpa only [before, Protocol.NamedStore.setClock] using hnew
  · have htime : eventTime = accepted := by
      obtain ⟨e, he, _, het⟩ := hacc.1.2
      have heq : NamedEvent.deliver reader (.block B) eventTime = e :=
        Option.some.inj (hdeliver.symm.trans he)
      simpa only [NamedEvent.time] using
        (congrArg NamedEvent.time heq).trans het
    subst eventTime
    right
    refine ⟨hdeliver, ?_⟩
    rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver] at hpost ⊢
    let pre := NamedRun.stateBefore S rho j reader
    have hpostOn : B ∈ (Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg pre.st B).bodies := by
      exact hpost
    exact block_new_body_stamp S pre.st B hpre hpostOn

/-- A full body whose retained first stamp is before a public cutoff was
already held at that cutoff's strict read. The observed body may come from any
other strict read; no ordering premise between `cut` and `read` is required. -/
theorem body_mem_stateBeforeTime_of_public_stampedBefore
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {reader : V} {cut read : Time} (hpublic : PublicTime S cut)
    {B : NamedBlock V}
    (hheld : B ∈ (NamedRun.stateBeforeTime S rho read reader).st.bodies)
    (hstamp : stampedBefore
      (NamedRun.stateBeforeTime S rho read reader).st.core.timestamp_block
      cut B.erase = true) :
    B ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  obtain ⟨n, hread, _⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  rw [hread] at hheld hstamp
  obtain hgen | ⟨j, hj, accepted, hacc⟩ :=
    NamedOutageProvenance.held_block_origin S rho n reader hheld
  · subst B
    obtain ⟨m, hcut, _⟩ :=
      Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
    rw [hcut]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho reader
      (Nat.zero_le m) (by
        simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
          Protocol.NamedStore.initial])
  · have hpost : B ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies := by
      simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
    by_contra hnotCut
    have hcutAccepted : cut ≤ accepted := by
      apply le_of_not_gt
      intro hearly
      obtain ⟨e, he, hnode, het⟩ := hacc.1.2
      apply hnotCut
      apply accepted_earlier_held_at_cut S rho sch hpublic he hnode
      · simpa only [← het] using hearly
      · exact hpost
    have htransport := NamedBlockStamp.stateBefore_body_stamp_mono
      S rho reader (Nat.succ_le_of_lt hj) hpost
    have hstampPost : stampedBefore
        (NamedRun.stateBefore S rho (j + 1) reader).st.core.timestamp_block
        cut B.erase = true := by
      unfold stampedBefore
      rw [← htransport.2]
      exact hstamp
    obtain ⟨e, he, hnode, het⟩ := hacc.1.2
    have hreader : reader ∈ rho.honest := by
      simpa only [hnode] using sch.honest_only e (List.mem_of_getElem? he)
    have hacceptedHorizon : accepted ≤ rho.horizon := by
      simpa only [het] using (sch.in_horizon e (List.mem_of_getElem? he)).2
    have hcutHorizon : cut ≤ rho.horizon :=
      hcutAccepted.trans hacceptedHorizon
    have htickMem := sch.tick_total reader hreader cut hpublic
      (publicTime_nonneg S hpublic) hcutHorizon
    obtain ⟨k, htick⟩ := List.mem_iff_getElem?.mp htickMem
    have hkj := tick_index_le_target_event rho sch htick he hnode
      (by simpa only [het] using hcutAccepted)
    rcases accepted_block_stamp_cases S rho hacc with
      ⟨hacceptTick, hpostStamp⟩ | ⟨hdeliver, hpostStamp⟩
    · unfold stampedBefore at hstampPost
      rw [hpostStamp] at hstampPost
      simp only [decide_eq_true_eq] at hstampPost
      exact (not_lt_of_ge (by exact_mod_cast hcutAccepted)) hstampPost
    · have hkne : k ≠ j := by
        intro hEq
        subst k
        rw [htick] at hdeliver
        cases hdeliver
      have hkjStrict : k < j := lt_of_le_of_ne hkj hkne
      have hclock := Proofs.NamedRuntime.tick_time_le_clock S rho sch.sorted
        (fun event hmem => (sch.in_horizon event hmem).1) htick hkjStrict
      unfold stampedBefore at hstampPost
      rw [hpostStamp] at hstampPost
      simp only [decide_eq_true_eq] at hstampPost
      have hclockStamp : (cut : Stamp) ≤
          ((NamedRun.stateBefore S rho j reader).st.core.t : Stamp) := by
        exact_mod_cast hclock
      exact (not_lt_of_ge hclockStamp) hstampPost

end DecoupledConsensusModel.Proofs.NamedPublicCutBody

end
