module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Goldfish confirmation counting after GST -/

/-- Recompute frozen viability with the candidate itself as the height witness.
The caller must supply both exact frozen processing and the block-local height
bound; full-tree membership is used only for finalized-root ancestry and the
selected FG-root filter. -/
theorem voterCandidate_of_processed_self_and_filtered
    (E : Env V) (st : Protocol.HealingStore V) {B : Block V}
    (hprocessed : B ∈
      Protocol.voter_processed_block_tree E st.toFG.toSG.toGoldfishStore st.s)
    (hheight : st.h_max - 1 ≤ (st.σ B).h)
    (hfiltered : B ∈ Protocol.get_filtered_block_tree st.toFG) :
    B ∈ Proofs.Optimistic.voter_candidate_tree E st := by
  have hdata := hfiltered
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨hprocessed, hdata.1.1.2⟩, B, hprocessed,
    Block.preceq_self B, hheight⟩, hdata.2⟩





private theorem recovery_admit_rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, Proofs.NamedAdmission.admit_row_bodies]

private theorem recovery_core_new_body (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Execution.NamedReceiptCalls.postCore S st B).bodies := by
  unfold Execution.NamedReceiptCalls.postCore
    Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost ⊢
    exact False.elim (hnew hpost)
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B.erase ∈ (Protocol.NamedStore.commitBlock st after B).core.T at hpost
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies
    unfold Protocol.NamedStore.commitBlock at hpost ⊢
    split_ifs at hpost ⊢ with hcond
    · simp
    · have hafter : B.erase ∈ after.T := by simpa using hpost
      exact False.elim (hcond ⟨hnew, hafter⟩)

private theorem recovery_on_block_new_body (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S st B).core.T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  rw [show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B =
      Protocol.NamedAdmission.admit_carried .alsoCarried S.hc st
        (Execution.NamedReceiptCalls.postCore S st B) B by rfl]
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · rw [recovery_admit_rows_bodies]
    exact recovery_core_new_body S st B hnew hpost
  · exact recovery_core_new_body S st B hnew hpost

/-! ## Actual Goldfish-vote handling -/

private def CoreVoteVisible (S : Setup V) (rho : Run V) (w : V) (n : Nat)
    (u : GoldfishVote V) : Prop :=
  (∃ k : Slot, u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k) ∨
    ∃ B ∈ (NamedRun.stateBefore S rho n w).st.bodies, u ∈ B.gf_votes

private theorem core_emits_of_voteVisible
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) {u : GoldfishVote V}
    (hu : CoreVoteVisible S rho w n u) (hx : u.val_index ∈ rho.honest) :
    ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
  have hblock : ∀ B : NamedBlock V,
      B ∈ (NamedRun.stateBefore S rho n w).st.bodies → u ∈ B.gf_votes →
        ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
    intro B hB hmem
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n B hB with
      rfl | ⟨j, e, -, -, hproc⟩
    · exact absurd hmem (by simp [NamedBlock.gf_votes])
    · exact (adm.carried_gf w B e.time hproc u hmem hx).imp fun _ ht => ht.2
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · obtain ⟨j, e, -, -, hproc⟩ :=
      Protocol.processes_gfVote_of_mem_pool S rho w n k u hk
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · exact (adm.unforgeable w (Object.gfVote u) e.time hbare
        u.val_index hx rfl).imp fun _ ht => ht.2
    · exact (adm.carried_gf w B e.time hprocB u hmem hx).imp fun _ ht => ht.2
  · exact hblock B hB hmem

/-- A pooled vote by an honest author has an authentic emission, under the
core execution contract. -/
theorem honestVote_emitted_of_mem_pool_stateBefore
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) (k : Slot) {u : GoldfishVote V}
    (hmem : u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k)
    (hx : u.val_index ∈ rho.honest) :
    ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t :=
  core_emits_of_voteVisible S adm w n (Or.inl ⟨k, hmem⟩) hx

private theorem core_voteVisible_unique
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) {u₁ u₂ : GoldfishVote V}
    (h₁ : CoreVoteVisible S rho w n u₁) (h₂ : CoreVoteVisible S rho w n u₂)
    (hx : u₁.val_index ∈ rho.honest) (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := core_emits_of_voteVisible S adm w n h₁ hx
  obtain ⟨t₂, he₂⟩ := core_emits_of_voteVisible S adm w n h₂ (by
    rw [hval]
    exact hx)
  rw [hval] at he₂
  exact Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed he₁ he₂ hslot

private theorem core_pool_no_honest_equivocation
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (w : V) (n : Nat) (k : Slot) {x : V} (hx : x ∈ rho.honest) :
    Protocol.equivocates ((NamedRun.stateBefore S rho n w).st.pool k) x = false := by
  have hps := Protocol.poolStamps_stateBefore
    S adm.toNamedScheduleWellFormed w n
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  simp only [Protocol.votes_by, Finset.mem_filter, Protocol.NamedStore.pool,
    Protocol.Store.pool, List.mem_toFinset] at hu₁ hu₂
  refine core_voteVisible_unique S adm w n
    (Or.inl ⟨k, hu₁.1⟩) (Or.inl ⟨k, hu₂.1⟩)
    (by rw [hu₁.2]; exact hx) (by rw [hu₂.2, hu₁.2]) ?_
  rw [hps.slot k u₁ hu₁.1, hps.slot k u₂ hu₂.1]

private theorem core_delivery_store_slot
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {u : GoldfishVote V}
    {s : Slot} {t' : Time}
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t'))
    (hlo : Protocol.vote_time S.E s ≤ t')
    (hhi : t' < Protocol.support_cutoff S.E s) :
    (NamedRun.stateBefore S rho i w).st.s = s := by
  have hclock : Protocol.vote_time S.E s ≤
      (NamedRun.stateBefore S rho i w).st.t := by
    refine Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed hi ?_ hlo
    exact adm.tick_total w hw _ (Proofs.Optimistic.publicTime_vote_time S s)
      (Proofs.Optimistic.vote_time_nonneg S.E s)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hup : (NamedRun.stateBefore S rho i w).st.t ≤ t' := by
    simpa [Event.time] using Protocol.store_time_le_event_time
      S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (NamedRun.stateBefore S rho i w).st.core.s = s
  rw [hslot]
  exact Proofs.Optimistic.slotOf_of_between S.E s hclock (lt_of_le_of_lt hup hhi)

private theorem core_goldfish_vote_with_fst_of_snd
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V)
    {u : GoldfishVote V}
    (h : (Protocol.goldfish_vote_with contract E hc nd st).2 = some u) :
    (Protocol.goldfish_vote_with contract E hc nd st).1 =
      Protocol.on_goldfish_vote st u := by
  simp only [Protocol.goldfish_vote_with] at h ⊢
  split_ifs at h ⊢ with hcommittee
  rw [← Option.some_inj.mp h]
  simp [Protocol.on_goldfish_vote_checked, hcommittee]

private theorem core_mem_pool_of_emits
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho w (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ rho.honest) :
    ∃ i : Nat,
      rho.events[i]? = some (.tick w (Protocol.vote_time S.E s)) ∧
      u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u = some c ∧
        c ≤ (Protocol.vote_time S.E s : Stamp) := by
  obtain ⟨i, hi, ho⟩ := hemit
  set t := Protocol.vote_time S.E s with htdef
  set n := NamedRun.stateBefore S rho i w with hndef
  obtain ⟨-, -, hduty, -, -⟩ := Proofs.Optimistic.gfVote_emitted_shape S w n t ho
  set gc := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadFrom S n t).cache with hgcdef
  have hreadSteq : (NamedActionReads.confirmationReadFrom S n t).st =
      Protocol.NamedStore.setClock S.E n.st t := rfl
  set st₀ := Protocol.NamedStore.setClock S.E n.st t with hst₀def
  have hduty' :
      (Protocol.goldfish_vote_with gc S.E S.hc (S.node w) st₀.core).2 = some u := by
    rw [← hreadSteq]
    exact hduty
  have hfst := core_goldfish_vote_with_fst_of_snd
    gc S.E S.hc (S.node w) st₀.core hduty'
  have hslot₀ : st₀.core.s = s := by
    show S.E.slotOf t = s
    rw [htdef]
    exact Proofs.Optimistic.slotOf_vote_time S.E s
  have hclock₀ : st₀.core.t = t := rfl
  have hpoolEq : st₀.core.pool s = n.st.core.pool s := rfl
  have hclockle : n.st.core.t ≤ t := by
    simpa [Event.time] using Protocol.store_time_le_event_time
      S adm.toNamedScheduleWellFormed hi w
  have hstamps₀ : Protocol.PoolStamps st₀.core := by
    exact (Protocol.poolStep_tickStore n.st.core t (S.E.slotOf t) hclockle
      (Protocol.poolStamps_stateBefore
        S adm.toNamedScheduleWellFormed w i)).2
  have hfresh : ¬ u.slot < st₀.core.s - 1 := by
    rw [hslot₀, hus]
    exact Nat.not_lt.mpr (Nat.sub_le s 1)
  have hfuture : ¬ st₀.core.s < u.slot := by
    rw [hslot₀, hus]
    exact lt_irrefl s
  have hequiv : Protocol.equivocates
      (st₀.core.pool u.slot) u.val_index = false := by
    rw [hus, hpoolEq]
    exact core_pool_no_honest_equivocation S adm w i s hval
  obtain ⟨hmem, c, hc, hle⟩ := Protocol.mem_and_stamp_of_process
    st₀.core u hstamps₀ hfresh hfuture hequiv
  rw [hus] at hmem
  set s' := S.E.slotOf t with hs'def
  set proposed := Protocol.NamedDuties.propose_block_with
    gc S.E S.hc S.cfg (S.node w) st₀ with hproposeddef
  set proposalDue := 0 < s' ∧ t = Protocol.proposal_time S.E s' ∧
    S.E.proposer s' = (S.node w).val_index with hproposalDuedef
  set st₁ := if proposalDue then proposed.1 else st₀ with hst₁def
  set voted := Protocol.NamedDuties.goldfish_vote_with
    gc S.E S.hc (S.node w) st₁ with hvoteddef
  set voteDue := 0 < s' ∧ t = Protocol.vote_time S.E s' with hvoteDuedef
  set st₂ := if voteDue then voted.1 else st₁ with hst₂def
  set st₃ := if 0 < s' ∧ t = Protocol.support_cutoff S.E s' then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st₂ (s' - 1)
    else st₂ with hst₃def
  have hs'eq : s' = s := by
    rw [hs'def, htdef]
    exact Proofs.Optimistic.slotOf_vote_time S.E s
  have hpne : ¬ proposalDue := by
    rw [hproposalDuedef]
    rintro ⟨-, hteq, -⟩
    exact Proofs.Optimistic.vote_time_ne_proposal_time S.E s'
      (by rw [← hteq, htdef, hs'eq])
  have hst₁eq : st₁ = st₀ := by rw [hst₁def, if_neg hpne]
  have hvd : voteDue := by
    rw [hvoteDuedef, hs'eq]
    exact ⟨hs, htdef⟩
  have hst₂eq : st₂.core = Protocol.on_goldfish_vote st₀.core u := by
    rw [hst₂def, if_pos hvd, hvoteddef, hst₁eq]
    exact hfst
  have hst₃fields :
      st₃.core.gf_votes = st₂.core.gf_votes ∧
      st₃.core.timestamp_vote = st₂.core.timestamp_vote := by
    rw [hst₃def]
    split_ifs <;> exact ⟨rfl, rfl⟩
  have htick₁eq :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st₃.core.s) ∧
          (S.node w).awake (S.hc.round_of st₃.core.s) = true then
        (Protocol.NamedDuties.attest_with
          gc S.E S.hc (S.node w) st₃ n.record).1
      else st₃ := by
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [st₃, st₂, voted, voteDue, st₁, proposed, proposalDue, s']
    split_ifs <;> rfl
  have hfinalfields :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1.core.gf_votes = st₃.core.gf_votes ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1.core.timestamp_vote = st₃.core.timestamp_vote := by
    rw [htick₁eq]
    split_ifs
    · obtain ⟨-, -, -, -, hgfv, htsv⟩ :=
        Proofs.NamedAdmission.admit_row_fixed_fields S.hc st₃
          (Protocol.NamedActions.round_action_with gc S.E S.hc
            (S.node w) st₃.core.toHealing n.record).2
      exact ⟨hgfv, htsv⟩
    · exact ⟨rfl, rfl⟩
  have hstepFull : NamedRun.stateBefore S rho (i + 1) w =
      (NamedNode.tick S w n t).1 := Proofs.NamedRuntime.stateBefore_tick S rho hi
  have hgcstep : (NamedNode.tick S w n t).1.st =
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
        n.st n.record t).1 := rfl
  refine ⟨i, hi, ?_, c, ?_, ?_⟩
  · show u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.core.gf_votes s
    rw [hstepFull, hgcstep, hfinalfields.1, hst₃fields.1, hst₂eq]
    exact hmem
  · show (NamedRun.stateBefore S rho (i + 1) w).st.core.timestamp_vote u = _
    rw [hstepFull, hgcstep, hfinalfields.2, hst₃fields.2, hst₂eq]
    exact hc
  · rw [← hclock₀]
    exact hle

private theorem actual_gfVote_settled_before_deadline
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hs : 0 < s) (hus : u.slot = s) (hval : u.val_index ∈ rho.honest)
    (hw : w ∈ rho.honest) (hlo : Protocol.vote_time S.E s ≤ t)
    (hcut : t < Protocol.support_cutoff S.E s) (hdeadline : t < Gamma) :
    ∃ i : Nat, ∃ e : Event V, rho.events[i]? = some e ∧ e.time < Gamma ∧
      (u ∈ beforeCutoff
          (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
          ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
        Protocol.equivocates
          (beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
          u.val_index = true) := by
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
      ⟨B, j', before, hcall⟩
  · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
      ⟨j, htick, hem⟩
    obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
        (Protocol.vote_time S.E s) := by
      simpa only [htVote] using hemit
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      core_mem_pool_of_emits S adm hs hemitVote hus hval
    refine ⟨i, _, hi, ?_, ?_⟩
    · simpa only [Event.time, htVote] using hdeadline
    · rw [beforeCutoff, Finset.mem_filter]
      apply Or.inl
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
          List.mem_toFinset, hus] using hmem
      · cases hstamp :
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u with
        | none => simp [stampedBefore, hstamp] at hc
        | some c' =>
          have hc' : c' < (Gamma : Stamp) := by
            have htime' : Protocol.vote_time S.E s < Gamma := by
              rw [← htVote]
              exact hdeadline
            have hcc : c' = c := Option.some.inj (hstamp.symm.trans hc)
            rw [hcc]
            exact lt_of_le_of_lt hle
              (WithBot.coe_lt_coe.mpr htime')
          simpa only [stampedBefore, hstamp, decide_eq_true_eq] using hc'
  · have heq : Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hslot : (NamedRun.stateBefore S rho j w).st.s = s :=
      core_delivery_store_slot S adm hw hdeliver hlo hcut
    have hfresh : ¬ u.slot < (NamedRun.stateBefore S rho j w).st.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (NamedRun.stateBefore S rho j w).st.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hequiv := core_pool_no_honest_equivocation S adm w j u.slot hval
    have hequiv' : ¬ Protocol.equivocates
        ((NamedRun.stateBefore S rho j w).st.pool u.slot) u.val_index = true := by
      intro hbad
      rw [hequiv] at hbad
      simp at hbad
    have hstamps : Protocol.PoolStamps
        (NamedRun.stateBefore S rho j w).st.core :=
      Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w j
    have hstep :
        (NamedRun.stateBefore S rho (j + 1) w).st.core =
          Protocol.on_goldfish_vote
            (NamedRun.stateBefore S rho j w).st.core u := by
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver]
      show Protocol.on_goldfish_vote_checked S.E _ u = _
      unfold Protocol.on_goldfish_vote_checked
      rw [if_neg (not_not.mpr hcommittee)]
    have hsettled :
        u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes u.slot ∧
          ∃ c : Stamp,
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
              c ≤ ((NamedRun.stateBefore S rho j w).st.t : Stamp) := by
      by_cases hdup : u ∈ (NamedRun.stateBefore S rho j w).st.gf_votes u.slot
      · obtain ⟨hmem, c, hc, hle⟩ := Protocol.mem_and_stamp_of_process
          (NamedRun.stateBefore S rho j w).st.core u hstamps hfresh hfuture hequiv
        refine ⟨?_, ?_⟩
        · show u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes u.slot
          rw [hstep]
          exact hmem
        · exact ⟨c, by
            change (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote u = some c
            rw [hstep]
            exact hc, hle⟩
      · obtain ⟨hmem, hc⟩ := Proofs.Optimistic.mem_pool_of_delivery S rho hdeliver
          hcommittee hfresh hfuture hdup hequiv'
        refine ⟨hmem, ?_⟩
        exact ⟨_, hc, le_refl _⟩
    have hprele : (NamedRun.stateBefore S rho j w).st.t ≤ t := by
      simpa [Event.time] using
        Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
          hdeliver w
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Event.time] using hdeadline
    · rw [beforeCutoff, Finset.mem_filter]
      apply Or.inl
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
          List.mem_toFinset, hus] using hsettled.1
      · obtain ⟨c, hc, hle⟩ := hsettled.2
        rw [stampedBefore, hc]
        simpa only [decide_eq_true_eq] using lt_of_le_of_lt hle
          (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hprele hdeadline))
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
    · have heq : Event.deliver w (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
        have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
          simpa [hbefore] using hB
        have hcoreB : B.erase ∈
            (NamedRun.stateBefore S rho j w).st.core.T := by
          rw [hcoh.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hB'
        simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
      have hclock0 : Protocol.vote_time S.E s ≤ before.core.t := by
        rw [hbefore]
        refine Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed
          hdeliver ?_ hlo
        exact adm.tick_total w hw _ (Proofs.Optimistic.publicTime_vote_time S s)
          (Proofs.Optimistic.vote_time_nonneg S.E s)
          (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hdeliver)).2)
      have hclockUp : before.core.t ≤ t := by
        rw [hbefore]
        simpa [Event.time] using
          Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
            hdeliver w
      have hslot : before.core.s = s := by
        have hsc := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho j w
        unfold Proofs.Optimistic.SlotOfClock at hsc
        have hsc' : before.core.s = S.E.slotOf before.core.t := by
          simpa [hbefore] using hsc
        rw [hsc']
        exact Proofs.Optimistic.slotOf_of_between S.E s hclock0
          (lt_of_le_of_lt hclockUp hcut)
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have hwire := adm.wire _ w (Object.block B) t hdeliver
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hcommittee := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcommittee
        exact hcommittee u huErase
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture (lt_of_le_of_lt hclockUp hdeadline)
      have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
        rw [hstate]
        simpa [final, hbefore, NamedReceipt.process]
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · simpa only [final, hfinalEq] using hlocal
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hproposal := congrArg Prod.snd
        (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
      have hgf0 : B.gf_votes =
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
            ((NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
        unfold Protocol.NamedDuties.propose_block_with at hproposal
        split at hproposal
        · cases hproposal
        · rename_i B' hB'
          have hBB' : B' = B := Option.some.inj hproposal
          rw [← hBB']
          exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
            S.E S.hc (S.node w) _ hB'
      have hgf' : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf0
      have hslot : before.core.s = s := by
        have hslot' := Proofs.Optimistic.slotOf_of_between S.E s hlo hcut
        simpa [hbefore, Protocol.NamedStore.setClock] using hslot'
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        have hrawStamps := Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
        have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              htick w
        exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf']
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot (before.core.s - 1) u huPool
      have hbad : s = s - 1 := by simpa [hus, hslot] using huslot
      have hltNat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hs) (by decide)
      exact False.elim ((Nat.ne_of_lt hltNat) hbad.symm)

private theorem actual_gfVote_settled_before_view_freeze
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ rho.honest)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s) (hdeadline : t < Gamma) :
    ∃ i : Nat, ∃ e : Event V, rho.events[i]? = some e ∧ e.time < Gamma ∧
      (u ∈ beforeCutoff
          (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
          ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
        Protocol.equivocates
          (beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
          u.val_index = true) := by
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
      ⟨B, jrow, before, hcall⟩
  · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
      ⟨j, htick, hem⟩
    obtain ⟨hs', ht', hval, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = Protocol.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hcut : t < Protocol.support_cutoff S.E s := by
      rw [htVote]
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hactual' : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t := by
      exact ⟨Or.inl (Or.inl ⟨t, htick, hem⟩), ⟨e, he, hnode, htime⟩⟩
    exact actual_gfVote_settled_before_deadline S adm.toNamedAdmissibleCore
      (s := S.E.slotOf t) hactual' hs' hus'
      (by rw [hval]; exact hw) hw (le_of_eq ht'.symm)
      (by simpa only [hslot] using hcut) hdeadline
  · have heq : Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have hslot : (NamedRun.stateBefore S rho j w).st.core.s = s := by
      show (NamedRun.stateBefore S rho j w).st.s = s
      exact Protocol.delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
    have hcommittee : u.val_index ∈ S.E.committee u.slot := by
      have hwire := adm.wire j w (Object.gfVote u) t hdeliver
      simpa only [Object.wellFormed, NamedReceipt.wellFormed,
        Protocol.vote_well_formed, decide_eq_true_eq] using hwire
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed w j
    have hfresh : ¬ u.slot < (NamedRun.stateBefore S rho j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (NamedRun.stateBefore S rho j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hclock : (NamedRun.stateBefore S rho j w).st.core.t < Gamma :=
      lt_of_le_of_lt
        (by
          show (NamedRun.stateBefore S rho j w).st.t ≤ t
          simpa [Event.time] using
            (Protocol.store_time_le_event_time S
              adm.toNamedScheduleWellFormed hdeliver w)) hdeadline
    have hlocal := Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates
      S.E (NamedRun.stateBefore S rho j w).st.core u Gamma hcommittee hstamps
      hfresh hfuture hclock
    have hstep :
        (NamedRun.stateBefore S rho (j + 1) w).st.core =
          Protocol.on_goldfish_vote_checked S.E
            (NamedRun.stateBefore S rho j w).st.core u := by
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver]
      rfl
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Event.time] using hdeadline
    · change u ∈ beforeCutoff
          (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
          ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
        Protocol.equivocates
          (beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
          u.val_index = true
      rw [hstep]
      exact hlocal
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
    · have heq : Event.deliver w (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
        have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
          simpa [hbefore] using hB
        rw [hbefore, hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB'
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        exact Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
      have hslot : before.core.s = s := by
        rw [hbefore]
        exact Protocol.delivery_store_slot_before_freeze S adm hw hdeliver hlo hhi
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have hwire := adm.wire _ w (Object.block B) t hdeliver
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hcommittee := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcommittee
        exact hcommittee u huErase
      have hclock : before.core.t < Gamma := by
        have hle : before.core.t ≤ t := by
          rw [hbefore]
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              hdeliver w
        exact lt_of_le_of_lt hle hdeadline
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture hclock
      have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
        rw [hstate]
        simpa [final, hbefore, NamedReceipt.process]
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · simpa only [final, hfinalEq] using hlocal
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hproposal := congrArg Prod.snd
        (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
      have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S w
        (NamedRun.stateBefore S rho j w) t hBemit
      have hguard := hshape.1
      have hgf0 : B.gf_votes =
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
            ((NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
        unfold Protocol.NamedDuties.propose_block_with at hproposal
        split at hproposal
        · cases hproposal
        · rename_i B' hB'
          have hBB' : B' = B := Option.some.inj hproposal
          rw [← hBB']
          exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
            S.E S.hc (S.node w) _ hB'
      have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        simpa [hbefore] using hgf0
      have hstamps : Protocol.PoolStamps before.core := by
        rw [hbefore]
        have hrawStamps := Protocol.poolStamps_stateBefore
          S adm.toNamedScheduleWellFormed w j
        have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
          simpa [Event.time] using
            Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed
              htick w
        exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf]
        exact List.mem_of_getElem? huindex
      have hslot : before.core.s = s + 1 := by
        have hslotTime : before.core.s = S.E.slotOf t := by
          rw [hbefore]
          rfl
        have hspos : 0 < before.core.s := by
          rw [hslotTime]
          exact hguard.1
        have hs' : s = before.core.s - 1 := by
          simpa only [hus] using hstamps.slot (before.core.s - 1) u huPool
        calc
          before.core.s = (before.core.s - 1) + 1 :=
            (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
          _ = s + 1 := by rw [← hs']
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have huPool' : u ∈
            (NamedRun.stateBefore S rho j w).st.core.gf_votes
              (before.core.s - 1) := by
          have hslotTime : before.core.s = S.E.slotOf t := by
            rw [hbefore]
            rfl
          have hpoolEq : before.core.gf_votes =
              (NamedRun.stateBefore S rho j w).st.core.gf_votes := by
            rw [hbefore]
            rfl
          rw [← hpoolEq]
          exact huPool
        have hcommittee' := CommitteePools.stateBefore S rho w j
          (before.core.s - 1) u huPool'
        have hs' := hstamps.slot (before.core.s - 1) u huPool
        simpa only [hs'] using hcommittee'
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslot]
        rw [Nat.add_sub_cancel]
        exact Nat.lt_irrefl s
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.not_lt.mpr (Nat.le_add_right s 1)
      have hclock : before.core.t < Gamma := by
        rw [hbefore]
        simpa [Event.time] using hdeadline
      have hpostBodies := recovery_on_block_new_body S before B hnew hcore
      have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
        S before B u Gamma hstamps (by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB) hpostBodies huErase
        hcommittee hfresh hfuture hclock
      let pre := NamedRun.stateBefore S rho j w
      let gc := NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S pre t).cache
      have hfields := Proofs.Optimistic.tick_fields_from_proposal gc S (S.node w)
        pre.st pre.record t (by simpa only [S.node_val_index] using hguard)
      let final := Protocol.NamedAdmission.on_block_with
        .alsoCarried S.E S.hc S.cfg before B
      have hproposalStage :
          (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
            (S.node w) before).1 = final := by
        have hpair := congrArg Prod.fst
          (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
        simpa only [gc, pre, final, hbefore] using hpair
      have hstate : NamedRun.stateBefore S rho (j + 1) w =
          (NamedNode.tick S w pre t).1 := Proofs.NamedRuntime.stateBefore_tick S rho htick
      have hgcstep : (NamedNode.tick S w pre t).1.st =
          (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
            pre.st pre.record t).1 := rfl
      have hfinalFields :
          (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes = final.core.gf_votes ∧
          (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote =
            final.core.timestamp_vote := by
        rw [hstate, hgcstep]
        have hguard' : 0 < S.E.slotOf t ∧
            t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
            S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
          simpa only [S.node_val_index] using hguard
        dsimp only at hfields
        rw [if_pos hguard'] at hfields
        have hproposalStage' :
            (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
              (S.node w) (Protocol.NamedStore.setClock S.E pre.st t)).1 = final := by
          simpa only [pre, hbefore] using hproposalStage
        rw [hproposalStage'] at hfields
        exact hfields
      have hlocal' : u ∈ beforeCutoff final.core.timestamp_vote Gamma
          (final.core.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff final.core.timestamp_vote Gamma (final.core.pool u.slot))
            u.val_index = true := by
        simpa only [final] using hlocal
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · change u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
            u.val_index = true
        simp only [Protocol.NamedStore.pool, Protocol.Store.pool]
        rw [hfinalFields.1, hfinalFields.2]
        exact hlocal'

#print axioms actual_gfVote_settled_before_deadline
#print axioms actual_gfVote_settled_before_view_freeze



private theorem gfVote_pooled_before_freeze_of_broadcast
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (hreceive : ∃ t', Protocol.vote_time S.E s ≤ t' ∧
      t' < Protocol.support_cutoff S.E s ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t') :
    ∃ (j : Nat) (e : Event V), rho.events[j]? = some e ∧
      e.time < Protocol.support_cutoff S.E s ∧
      u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
          c < (Protocol.support_cutoff S.E s : Stamp) := by
  obtain ⟨-, -, hvalv, -⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
  have hval : u.val_index ∈ rho.honest := by
    rw [hvalv]
    exact hv
  obtain ⟨t', hlo, hhi, j, hactual⟩ := hreceive
  obtain ⟨i, e, he, hearly, hsettled⟩ :=
    actual_gfVote_settled_before_deadline S adm hactual hs hus hval hw hlo
      hhi hhi
  rcases hsettled with hmem | hequiv
  · rw [beforeCutoff, Finset.mem_filter] at hmem
    obtain ⟨hpool, hstamp⟩ := hmem
    cases hc : (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u with
    | none => simp [stampedBefore, hc] at hstamp
    | some c =>
        have hc' : c < (Protocol.support_cutoff S.E s : Stamp) := by
          simpa only [stampedBefore, hc, decide_eq_true_eq] using hstamp
        refine ⟨i, e, he, hearly, ?_, c, hc, hc'⟩
        simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
          List.mem_toFinset, hus] using hpool
  · have hfull : Protocol.equivocates
        ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot)
        u.val_index = true :=
      equivocates_mono (by
        intro x hx
        exact (Finset.mem_filter.mp hx).1) u.val_index hequiv
    have hno := core_pool_no_honest_equivocation
      S adm w (i + 1) u.slot hval
    rw [hno] at hfull
    simp at hfull

private theorem gfVote_pooled_before_freeze_after_gst
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ (j : Nat) (e : Event V), rho.events[j]? = some e ∧
      e.time < Protocol.support_cutoff S.E s ∧
      u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
          c < (Protocol.support_cutoff S.E s : Stamp) := by
  apply gfVote_pooled_before_freeze_of_broadcast S adm hv hs hemit hus hw
  obtain ⟨t', hlo, hhi, j, hactual⟩ :=
    broadcast_after_gst S adm hv hw hpost hemit
      (by rw [Proofs.Optimistic.vote_time_add_delta]; exact hhor) rfl
  rw [Proofs.Optimistic.vote_time_add_delta] at hhi
  exact ⟨t', hlo, hhi, j, hactual⟩

private theorem gfVote_pooled_before_freeze_of_delivery
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (hcap : Protocol.support_cutoff S.E s ≤ cap) :
    ∃ (j : Nat) (e : Event V), rho.events[j]? = some e ∧
      e.time < Protocol.support_cutoff S.E s ∧
      u ∈ (NamedRun.stateBefore S rho (j + 1) w).st.gf_votes s ∧
      ∃ c : Stamp,
        (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote u = some c ∧
          c < (Protocol.support_cutoff S.E s : Stamp) := by
  apply gfVote_pooled_before_freeze_of_broadcast S adm hv hs hemit hus hw
  obtain ⟨t', hlo, hhi, j, hactual⟩ :=
    hdelivery.broadcast v hv (Object.gfVote u)
      (Protocol.vote_time S.E s) hemit w hw
      (by rw [Proofs.Optimistic.vote_time_add_delta]; exact hcap) rfl
  rw [Proofs.Optimistic.vote_time_add_delta] at hhi
  exact ⟨t', hlo, hhi, j, hactual⟩

theorem gfVote_in_cutoff_view_after_gst
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (Gamma Gamma' : Time)
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    (hGamma' : Protocol.support_cutoff S.E s ≤ Gamma')
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff (Run.storeBeforeTime S rho w Gamma).timestamp_vote Gamma'
      ((Run.storeBeforeTime S rho w Gamma).pool s) := by
  obtain ⟨j, e, hj, hjt, hmem, c, hc, hlt⟩ :=
    gfVote_pooled_before_freeze_after_gst S adm hv hs hpost hemit hus hw hhor
  have hjN : j <
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length := by
    by_contra hcon
    have h := Proofs.Optimistic.filter_false_of_index_ge
      S adm.toNamedScheduleWellFormed _
        (Proofs.Optimistic.downward_lt Gamma)
        (Nat.le_of_not_lt hcon) hj
    simp only [decide_eq_false_iff_not, not_lt] at h
    exact absurd (lt_of_lt_of_le hjt hGamma) (not_lt_of_ge h)
  have hcarry : Protocol.PoolCarry
      (NamedRun.stateBefore S rho (j + 1) w).st.core
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed w
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length hjN
  have hstore : Run.storeBeforeTime S rho w Gamma =
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st := by
    change (NamedRun.stateBeforeTime S rho Gamma w).st = _
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
        S adm.toNamedScheduleWellFormed Gamma) w)]
  rw [hstore, beforeCutoff, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simpa only [Protocol.Store.pool, List.mem_toFinset] using hcarry.mem s u hmem
  simp only [stampedBefore, hcarry.stamp u c hc, decide_eq_true_eq]
  exact lt_of_lt_of_le hlt (by exact_mod_cast hGamma')

/-- Delivery-parametric twin of `gfVote_in_cutoff_view_after_gst`. -/
theorem gfVote_in_cutoff_view_of_delivery
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s)
    {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho v (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ rho.honest)
    (Gamma Gamma' : Time)
    (hGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    (hGamma' : Protocol.support_cutoff S.E s ≤ Gamma')
    (hcap : Protocol.support_cutoff S.E s ≤ cap) :
    u ∈ beforeCutoff (Run.storeBeforeTime S rho w Gamma).timestamp_vote Gamma'
      ((Run.storeBeforeTime S rho w Gamma).pool s) := by
  obtain ⟨j, e, hj, hjt, hmem, c, hc, hlt⟩ :=
    gfVote_pooled_before_freeze_of_delivery S adm hdelivery hv hs hemit hus hw hcap
  have hjN : j <
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length := by
    by_contra hcon
    have h := Proofs.Optimistic.filter_false_of_index_ge
      S adm.toNamedScheduleWellFormed _
        (Proofs.Optimistic.downward_lt Gamma)
        (Nat.le_of_not_lt hcon) hj
    simp only [decide_eq_false_iff_not, not_lt] at h
    exact absurd (lt_of_lt_of_le hjt hGamma) (not_lt_of_ge h)
  have hcarry : Protocol.PoolCarry
      (NamedRun.stateBefore S rho (j + 1) w).st.core
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed w
      (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length hjN
  have hstore : Run.storeBeforeTime S rho w Gamma =
      (NamedRun.stateBefore S rho
        (rho.events.filter (fun x : Event V => decide (x.time < Gamma))).length w).st := by
    change (NamedRun.stateBeforeTime S rho Gamma w).st = _
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
        S adm.toNamedScheduleWellFormed Gamma) w)]
  rw [hstore, beforeCutoff, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simpa only [Protocol.Store.pool, List.mem_toFinset] using hcarry.mem s u hmem
  simp only [stampedBefore, hcarry.stamp u c hc, decide_eq_true_eq]
  exact lt_of_lt_of_le hlt (by exact_mod_cast hGamma')

#print axioms gfVote_in_cutoff_view_after_gst
#print axioms gfVote_in_cutoff_view_of_delivery
#print axioms honestVote_emitted_of_mem_pool_stateBefore


/-- A next-slot vote-duty FG root below `B` pins the receiver's finalized root
below `B` at every earlier delivery before the preceding view freeze.

Named-runtime proof: the delivery witness `X` is a
`NamedBlock V` (/C1: `Object.block` now carries a named body); `F ⪯ J` for
the confirmation-time read comes from `NamedJustificationBound`'s premise-free
producer, not the retired `Proofs.Bridges.depReachable_stateBeforeTime` /
`reachableStore_of_depReachableStore` pair. -/
private theorem finalized_preceq_at_delivery_of_voteDutyRoot_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.view_freeze S.E s) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.vote_time S.E (s + 1)
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_trans hlt (view_freeze_lt_vote_time_succ S.E s))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Gamma) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    (Proofs.NamedJustificationBound.storeFinality_stateBeforeTime S rho Gamma v).2
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')


private theorem gfVote_processes_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  obtain ⟨i, e, he, htime, hsettled⟩ :=
    actual_gfVote_settled_before_view_freeze S adm hproc
      hus hw hlo hhi hhi
  let Gamma := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := e)
        (by simpa [N] using hNle) he
    have hfreezeSucc : Protocol.view_freeze S.E s < Gamma := by
      simpa only [Gamma] using view_freeze_lt_vote_time_succ S.E s
    exact (not_le_of_gt (lt_trans htime hfreezeSucc)) hGammae
  have hcarry : Protocol.PoolCarry
      (NamedRun.stateBefore S rho (i + 1) w).st.core
      (NamedRun.stateBefore S rho N w).st.core :=
    Protocol.pool_carry S adm.toNamedScheduleWellFormed w N
      (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (NamedRun.stateBefore S rho N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
        S adm.toNamedScheduleWellFormed Gamma) w)]
  rw [hus] at hsettled
  rcases hsettled with hmem | hequiv
  · apply Or.inl
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s (Protocol.view_freeze S.E s) hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [hstore]
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      beforeCutoff_subset_of_poolCarry hcarry s (Protocol.view_freeze S.E s) hx

#print axioms gfVote_processes_settled_at_voteDuty_after_gst

private theorem accepted_gfVote_forward_settled_at_voteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.support_cutoff S.E s)
    (hhor : Protocol.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ∨
      Protocol.equivocates
        (beforeCutoff
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
          (Protocol.view_freeze S.E s)
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s))
        u.val_index = true := by
  by_cases halready : Object.processed
      (NamedRun.stateBefore S rho (i + 1) w).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply gfVote_processed_after_event_at_voteDuty S adm he hus halready
    simpa only [het] using
      lt_trans hhi (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
  · have hunaccepted : Object.processed
        (NamedRun.stateBefore S rho (i + 1) w).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := by
      have hlt : t + S.E.Δ < Protocol.view_freeze S.E s := by
        calc
          t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
            Int.add_lt_add_right hhi S.E.Δ
          _ = Protocol.view_freeze S.E s :=
            support_cutoff_add_delta_eq_view_freeze S.E s
      exact le_trans (le_of_lt hlt) hhor
    have hpostAcceptance : S.E.t_GST ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j, hproc⟩ :=
      relay_gf_vote_after_gst S adm hv hw hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeFreeze : t' < Protocol.view_freeze S.E s := by
      exact lt_trans hdeadline (by
        calc
          t + S.E.Δ < Protocol.support_cutoff S.E s + S.E.Δ :=
            Int.add_lt_add_right hhi S.E.Δ
          _ = Protocol.view_freeze S.E s :=
            support_cutoff_add_delta_eq_view_freeze S.E s)
    exact gfVote_processes_settled_at_voteDuty_after_gst
      S adm hw hpost hproc hus (le_trans hlo hcausal) hbeforeFreeze hhor

#print axioms accepted_gfVote_forward_settled_at_voteDuty_after_gst

private theorem actual_gfVote_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hactual : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ rho.honest)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  let Gamma := Protocol.confirmation_time S.E s
  have carry_to_conf :
      ∀ (i : Nat) (e : Event V),
        rho.events[i]? = some e → e.time < Gamma →
        (u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot) ∨
          Protocol.equivocates
            (beforeCutoff
              (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (i + 1) w).st.pool u.slot))
            u.val_index = true) →
        u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
          Protocol.equivocates
            (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
            u.val_index = true := by
    intro i e hi hetime hlocal
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
          (t := Gamma) (j := i) (e := e)
          (by simpa [N] using hNle) hi
      exact (not_le_of_gt hetime) hGammae
    have hcarry : Protocol.PoolCarry
        (NamedRun.stateBefore S rho (i + 1) w).st.core
        (NamedRun.stateBefore S rho N w).st.core :=
      Protocol.pool_carry S adm.toNamedScheduleWellFormed w N
        (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho w s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N w).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) w)]
    rw [hus] at hlocal
    rcases hlocal with hmem | hequiv
    · apply Or.inl
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hmem
    · apply Or.inr
      apply equivocates_mono _ u.val_index hequiv
      intro x hx
      rw [confLate, hstore, Proofs.Optimistic.tickStore]
      exact beforeCutoff_subset_of_poolCarry hcarry s Gamma hx
  by_cases hfreeze : t < Protocol.view_freeze S.E s
  · obtain ⟨i, e, hi, hetime, hlocal⟩ :=
      actual_gfVote_settled_before_view_freeze S adm hactual hus hw hlo hfreeze hhi
    exact carry_to_conf i e hi hetime hlocal
  · obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
    simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
    rcases hindex with (⟨t', htick, hem⟩ | ⟨t', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
    · have heq : Event.tick w t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      have hemit : NamedRun.emits S rho w (Object.gfVote u) t :=
        ⟨j, htick, hem⟩
      obtain ⟨hs', ht', -, hus'⟩ := Proofs.Optimistic.emits_gfVote_shape S hemit
      have hslot : S.E.slotOf t = s := by rw [← hus', hus]
      have htVote : t = Protocol.vote_time S.E s := by
        simpa only [hslot] using ht'
      have hemitVote : NamedRun.emits S rho w (Object.gfVote u)
          (Protocol.vote_time S.E s) := by
        simpa only [htVote] using hemit
      have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
        le_trans hpost (le_of_lt (by
          unfold Protocol.vote_time
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos))
      have hsupport : Protocol.support_cutoff S.E s ≤
          Protocol.confirmation_time S.E s :=
        support_cutoff_le_confirmation_time S.E s
      have hrecv := gfVote_in_cutoff_view_after_gst
        S adm.toNamedAdmissibleCore hw (by simpa only [hslot] using hs')
          hpostVote hemitVote hus hw
        (Protocol.confirmation_time S.E s)
        (Protocol.confirmation_time S.E s)
        hsupport hsupport (le_trans hsupport hhor)
      apply Or.inl
      simpa only [confLate, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Protocol.NamedStore.pool, Protocol.Store.pool] using hrecv
    · have heq : Event.deliver w (Object.gfVote u) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact gfVote_delivery_settled_at_confStore S adm hw hdeliver hus hlo hhi
    · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
      have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
      have huErase : u ∈ B.erase.gf_votes := by
        rwa [Proofs.NamedWire.erase_goldfish_votes]
      rcases hblock with
          ⟨t', hdeliver, hbefore⟩ | ⟨t', htick, hBemit, hbefore⟩
      · have heq : Event.deliver w (Object.block B) t' = e :=
          Option.some.inj (hdeliver.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hpostBodies := recovery_on_block_new_body S before B hnew hcore
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          exact Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
        have hslot : before.core.s = s ∨ before.core.s = s + 1 := by
          rw [hbefore]
          exact Protocol.delivery_store_slot_before_confirmation
            S adm hw hdeliver hlo hhi
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.sub_le s 1)
          · rw [hus, hs, Nat.add_sub_cancel]
            exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.lt_irrefl s
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have hwire := adm.wire _ w (Object.block B) t hdeliver
          simp only [Object.wellFormed, NamedReceipt.wellFormed,
            Bool.and_eq_true] at hwire
          have hcarried := hwire.2
          simp only [List.all_eq_true, decide_eq_true_eq] at hcarried
          exact hcarried u huErase
        have hclock : before.core.t < Gamma := by
          have hle : before.core.t ≤ t := by
            rw [hbefore]
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed hdeliver w
          exact lt_of_le_of_lt hle hhi
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        have hstate := Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hfinalEq : (NamedRun.stateBefore S rho (j + 1) w).st = final := by
          rw [hstate]
          simpa [final, hbefore, NamedReceipt.process]
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          simpa only [final, hfinalEq] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'
      · have heq : Event.tick w t' = e :=
          Option.some.inj (htick.symm.trans he)
        have htt : t' = t := (congrArg Event.time heq).trans htime
        subst t'
        have hproposal := congrArg Prod.snd
          (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
        have hshape := Proofs.HealingSurface.block_mem_on_tick_emit S w
          (NamedRun.stateBefore S rho j w) t hBemit
        have hguard := hshape.1
        have hgf0 : B.gf_votes =
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho j w) t).st.core.gf_votes
              ((NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho j w) t).st.core.s - 1) := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · rename_i B' hB'
            have hBB' : B' = B := Option.some.inj hproposal
            rw [← hBB']
            exact Proofs.Optimistic.proposal_with_gf_votes _ .poolAndCarried
              S.E S.hc (S.node w) _ hB'
        have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
          simpa [hbefore] using hgf0
        have hstamps : Protocol.PoolStamps before.core := by
          rw [hbefore]
          have hrawStamps := Protocol.poolStamps_stateBefore
            S adm.toNamedScheduleWellFormed w j
          have htle : (NamedRun.stateBefore S rho j w).st.core.t ≤ t := by
            simpa [Event.time] using
              Protocol.store_time_le_event_time S
                adm.toNamedScheduleWellFormed htick w
          exact (Protocol.poolStep_tickStore _ _ _ htle hrawStamps).2
        have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
          rw [← hgf]
          exact List.mem_of_getElem? huindex
        have hslot : before.core.s = s + 1 := by
          have hslotTime : before.core.s = S.E.slotOf t := by
            rw [hbefore]
            rfl
          have hspos : 0 < before.core.s := by
            rw [hslotTime]
            exact hguard.1
          have hs' : s = before.core.s - 1 := by
            simpa only [hus] using hstamps.slot (before.core.s - 1) u huPool
          calc
            before.core.s = (before.core.s - 1) + 1 :=
              (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
            _ = s + 1 := by rw [← hs']
        have hcommittee : u.val_index ∈ S.E.committee u.slot := by
          have huPool' : u ∈
              (NamedRun.stateBefore S rho j w).st.core.gf_votes
                (before.core.s - 1) := by
            have hpoolEq : before.core.gf_votes =
                (NamedRun.stateBefore S rho j w).st.core.gf_votes := by
              rw [hbefore]
              rfl
            rw [← hpoolEq]
            exact huPool
          have hcommittee' := CommitteePools.stateBefore S rho w j
            (before.core.s - 1) u huPool'
          have hs' := hstamps.slot (before.core.s - 1) u huPool
          simpa only [hs'] using hcommittee'
        have hfresh : ¬ u.slot < before.core.s - 1 := by
          rw [hus, hslot, Nat.add_sub_cancel]
          exact Nat.lt_irrefl s
        have hfuture : ¬ before.core.s < u.slot := by
          rw [hslot, hus]
          exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hclock : before.core.t < Gamma := by
          rw [hbefore]
          simpa [Event.time] using hhi
        have hpostBodies := recovery_on_block_new_body S before B hnew hcore
        have hpreBodies : B ∉ before.bodies := by
          intro hB
          apply hnew
          have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j w).1.1.1
          have hB' : B ∈ (NamedRun.stateBefore S rho j w).st.bodies := by
            simpa [hbefore] using hB
          have hcoreB : B.erase ∈
              (NamedRun.stateBefore S rho j w).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hB'
          simpa [hbefore, Protocol.NamedStore.setClock] using hcoreB
        have hlocal := Proofs.Optimistic.block_carried_before_deadline_or_equivocates
          S before B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        let pre := NamedRun.stateBefore S rho j w
        let gc := NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S pre t).cache
        have hfields := Proofs.Optimistic.tick_fields_from_proposal gc S (S.node w)
          pre.st pre.record t (by simpa only [S.node_val_index] using hguard)
        let final := Protocol.NamedAdmission.on_block_with
          .alsoCarried S.E S.hc S.cfg before B
        have hproposalStage :
            (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
              (S.node w) before).1 = final := by
          have hpair := congrArg Prod.fst
            (Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hBemit)
          simpa only [gc, pre, final, hbefore] using hpair
        have hstate : NamedRun.stateBefore S rho (j + 1) w =
            (NamedNode.tick S w pre t).1 :=
          Proofs.NamedRuntime.stateBefore_tick S rho htick
        have hgcstep : (NamedNode.tick S w pre t).1.st =
            (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w)
              pre.st pre.record t).1 := rfl
        have hfinalFields :
            (NamedRun.stateBefore S rho (j + 1) w).st.core.gf_votes =
                final.core.gf_votes ∧
            (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote =
                final.core.timestamp_vote := by
          rw [hstate, hgcstep]
          have hguard' : 0 < S.E.slotOf t ∧
              t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
              S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
            simpa only [S.node_val_index] using hguard
          dsimp only at hfields
          rw [if_pos hguard'] at hfields
          have hproposalStage' :
              (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                (S.node w)
                (Protocol.NamedStore.setClock S.E pre.st t)).1 = final := by
            simpa only [pre, hbefore] using hproposalStage
          rw [hproposalStage'] at hfields
          exact hfields
        have hlocal' : u ∈ beforeCutoff
            (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
            ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.pool u.slot))
              u.val_index = true := by
          change u ∈ beforeCutoff
              (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
              ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot) ∨
            Protocol.equivocates
              (beforeCutoff
                (NamedRun.stateBefore S rho (j + 1) w).st.core.timestamp_vote Gamma
                ((NamedRun.stateBefore S rho (j + 1) w).st.core.pool u.slot))
              u.val_index = true
          simp only [Protocol.NamedStore.pool, Protocol.Store.pool]
          rw [hfinalFields.1, hfinalFields.2]
          simpa only [final] using hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'

private theorem gfVote_processes_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest)
    {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hproc : NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s)
        u.val_index = true := by
  exact actual_gfVote_settled_at_confStore_after_gst
    S adm hpost hproc hus hw hlo hhi hhor


private theorem accepted_gfVote_backward_settled_at_confStore_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hacc : NamedRun.acceptsAt S rho i w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.vote_time S.E (s + 1))
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  by_cases halready :
      Object.processed (NamedRun.stateBefore S rho (i + 1) v).st
        (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have hmem : u ∈ (NamedRun.stateBefore S rho (i + 1) v).st.gf_votes s := by
      simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq,
        Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset] at halready
      rwa [hus] at halready
    have hstamps := Protocol.poolStamps_stateBefore
      S adm.toNamedScheduleWellFormed v (i + 1)
    obtain ⟨c, hc⟩ : ∃ c : Stamp,
        (NamedRun.stateBefore S rho (i + 1) v).st.timestamp_vote u = some c :=
      Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
    have hclock : (NamedRun.stateBefore S rho (i + 1) v).st.t ≤ e.time :=
      Protocol.block_store_time_after_event_le
        S adm.toNamedScheduleWellFormed he v
    have hvoteConf : Protocol.vote_time S.E (s + 1) <
        Protocol.confirmation_time S.E s := by
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hcConf : c < (Protocol.confirmation_time S.E s : Stamp) :=
      lt_of_le_of_lt (hstamps.bounded u c hc)
        (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock (by
          rw [het]
          exact lt_trans hhi hvoteConf)))
    let Gamma := Protocol.confirmation_time S.E s
    let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hGammae : Gamma ≤ e.time :=
        Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
          (t := Gamma) (j := i) (e := e)
          (by simpa only [N] using hNle) he
      rw [het] at hGammae
      exact (not_le_of_gt (lt_trans hhi hvoteConf)) hGammae
    have hcarry : Protocol.PoolCarry
        (NamedRun.stateBefore S rho (i + 1) v).st.core
        (NamedRun.stateBefore S rho N v).st.core :=
      Protocol.pool_carry S adm.toNamedScheduleWellFormed v N
        (Nat.succ_le_of_lt hiN)
    have hstore : Proofs.Optimistic.confStore S rho v s =
        Proofs.Optimistic.tickStore S (NamedRun.stateBefore S rho N v).st.core Gamma := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed Gamma) v)]
    apply Or.inl
    rw [confLate, hstore, beforeCutoff, Finset.mem_filter, Protocol.Store.pool,
      List.mem_toFinset]
    refine ⟨hcarry.mem s u hmem, ?_⟩
    simp only [Proofs.Optimistic.tickStore, stampedBefore, hcarry.stamp u c hc,
      decide_eq_true_eq]
    exact hcConf
  · have hunaccepted :
      Object.processed (NamedRun.stateBefore S rho (i + 1) v).st
        (Object.gfVote u) = false :=
    Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := by
      have hlt : t + S.E.Δ < Protocol.confirmation_time S.E s := by
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.add_lt_add_right hhi S.E.Δ
      exact le_trans (le_of_lt hlt) hhor
    have hpostAcceptance : S.E.t_GST ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      relay_gf_vote_after_gst S adm hw hv hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeConf : t' < Protocol.confirmation_time S.E s :=
      lt_trans hdeadline (by
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.add_lt_add_right hhi S.E.Δ)
    exact gfVote_processes_settled_at_confStore_after_gst
      S adm hv hpost hproc hus (le_trans hlo hcausal) hbeforeConf hhor




private theorem targetPoolVote_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {u : GoldfishVote V}
    (hu : u ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
        u.val_index = true := by
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    HonestWeightMajority.targetPoolVoteAcceptedBeforeVote S adm hu
  exact accepted_gfVote_backward_settled_at_confStore_after_gst
    S adm hv hw hpost hacc hus hlo hhi hhor

private theorem targetPoolEquivocates_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) {x : V}
    (hequiv : Protocol.equivocates
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x = true) :
    Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true := by
  by_cases hsource : Protocol.equivocates
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x = true
  · exact hsource
  rw [Protocol.equivocates, decide_eq_true_eq] at hequiv ⊢
  have hsub :
      Protocol.votes_by
          ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) x ⊆
        Protocol.votes_by
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) x := by
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    refine ⟨?_, hu.2⟩
    rcases targetPoolVote_settledAtSource_after_gst
        S adm hv hw hpost hhor hu.1 with hmem | hequivSource
    · exact hmem
    · rw [hu.2] at hequivSource
      exact False.elim (hsource hequivSource)
  exact le_trans hequiv (Finset.card_le_card hsub)

private theorem targetRawVote_settledAtSource_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    ∀ u ∈ Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1),
      u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v s) s ∨
        Protocol.equivocates
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
          u.val_index = true := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union] at hu
  rcases hu with hreceipt | hcarried
  · rw [Nat.add_sub_cancel] at hreceipt
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      targetReceiptVotesAcceptedInWindow_of_admissible S adm hw s u hreceipt
    exact accepted_gfVote_backward_settled_at_confStore_after_gst
      S adm hv hw hpost hacc hus hlo
        (lt_trans hhi (view_freeze_lt_vote_time_succ S.E s)) hhor
  · rw [Finset.mem_biUnion] at hcarried
    obtain ⟨B, hB, huB⟩ := hcarried
    rw [Finset.mem_filter] at hB huB
    have hus : u.slot = s := by
      simpa only [Nat.add_sub_cancel] using huB.2
    have huList : u ∈ B.gf_votes := List.mem_toFinset.mp huB.1
    rcases HonestWeightMajority.targetCarrierVote_settledInPool
        S adm hw hB.1 hB.2 huList hus with hpool | hequiv
    · exact targetPoolVote_settledAtSource_after_gst
        S adm hv hw hpost hhor hpool
    · exact Or.inr
        (targetPoolEquivocates_settledAtSource_after_gst
          S adm hv hw hpost hhor hequiv)

#print axioms targetPoolVote_settledAtSource_after_gst
#print axioms targetPoolEquivocates_settledAtSource_after_gst
#print axioms targetRawVote_settledAtSource_after_gst

private theorem supportingTarget_visibleAtVoteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
    {H : Block V}
    (hfind : Block.find? (Proofs.Optimistic.confStore S rho v s).T u.head = some H)
    (hBH : Block.Preceq B H) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T u.head = some H ∧
      stampedBefore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_block
        (Protocol.view_freeze S.E s) H = true ∧
      (H = Block.genesis ∨
        AdmittedBefore S rho w H (Protocol.view_freeze S.E s)) := by
  by_cases hgen : H = Block.genesis
  · subst H
    have hvisible := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
      (Protocol.view_freeze S.E s)
    have hmem : Block.genesis ∈
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hvisible.1
    refine ⟨HonestWeightMajority.find_voteDutyStore_of_source_find_and_mem
      S adm hw hfind hmem, ?_, Or.inl rfl⟩
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hvisible.2
  · have hHsource : H ∈ (Proofs.Optimistic.confStore S rho v s).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v s) s :=
      (Finset.mem_filter.mp hu).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).tau
        (Protocol.support_cutoff S.E s) u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore
        (Proofs.Optimistic.confStore S rho v s).timestamp_block
        (Protocol.support_cutoff S.E s) H = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
    have hHn : H ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hn] using hHsource
    obtain ⟨C, hCmem, hCerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hHn
    have hprocessed : Object.processed
        (rho.stateBefore S n v).st (Object.block C) = true := by
      simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
        using hCmem
    obtain hgen' | ⟨i, hin, t, hacc⟩ :=
      acceptsAt_block_of_processed S rho v n C hprocessed
    · exact False.elim (hgen (by rw [← hCerase, hgen']; rfl))
    · have hstampn : stampedBefore
          (rho.stateBefore S n v).st.core.timestamp_block
          (Protocol.support_cutoff S.E s) C.erase = true := by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
          Run.storeBeforeTime, hn, hCerase] using hHstamp
      have htSupport : t < Protocol.support_cutoff S.E s :=
        HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hv hacc (Nat.succ_le_of_lt hin)
            (publicTime_support_cutoff S s) hstampn
      have hCposErase : 0 < C.erase.slot :=
        Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
      have hCpos : 0 < C.slot := by
        simpa only [Proofs.NamedWire.erase_slot] using hCposErase
      have hBH' : Block.Preceq B C.erase := by
        simpa only [hCerase] using hBH
      have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
        apply le_trans _ hhor
        exact le_of_lt (lt_trans
          (Int.lt_add_of_pos_right _ S.E.Δ_pos)
          (view_freeze_add_delta_lt_confirmation_time S.E s))
      have hpostCut : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
        apply le_trans hpost
        unfold Protocol.proposal_time Protocol.support_cutoff
        exact le_add_of_nonneg_right
          (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
      have hadmitC : AdmittedBefore S rho w C.erase
          (Protocol.view_freeze S.E s) := by
        apply Protocol.block_admittedBefore_of_accepted_after_cutoff
          S adm hv hw hCpos hacc htSupport hpostCut
            (support_cutoff_add_delta_eq_view_freeze S.E s) hfreezeHor
        intro j hj
        have hjVote := hj.trans (Proofs.strict_filter_length_mono rho
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
        have hroot' : Block.Preceq
            (Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).toHealing.toFG)
              B := by
          simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore] using hroot
        exact Block.preceq_trans
          (Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
            S rho adm.toNamedScheduleWellFormed.sorted hroot' hjVote) hBH'
      have hvisible := admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmitC
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      have hmem : H ∈ (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T := by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, hCerase] using hvisible.1
      refine ⟨HonestWeightMajority.find_voteDutyStore_of_source_find_and_mem
        S adm hw hfind hmem, ?_, Or.inr (by simpa only [hCerase] using hadmitC)⟩
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, hCerase] using hvisible.2

#print axioms supportingTarget_visibleAtVoteDuty_after_gst

theorem adoptionTransport_B_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B) :
    AdoptionTransport
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
      (Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
          (s + 1)) B := by
  refine ⟨?_, targetRawVote_settledAtSource_after_gst
    S adm hv hw hpost hhor⟩
  intro u hu htargets
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    confirmationVotesAcceptedInWindow_of_admissible S adm hv s u hu
  have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
    apply le_trans _ hhor
    exact le_of_lt (lt_trans
      (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (view_freeze_add_delta_lt_confirmation_time S.E s))
  have hsettled := accepted_gfVote_forward_settled_at_voteDuty_after_gst
    S adm hv hw hpost hacc hus hlo hhi hfreezeHor
  have hvisible := supportingTarget_visibleAtVoteDuty_after_gst
    S adm hv hw hpost hhor hroot hu hfind hBH.2
  rcases settled_before_freeze_in_voter_pair S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)) s
      hvisible.1 hvisible.2.1 hBH.1 hsettled with hsupport | hequiv
  · exact Or.inl ⟨hsupport,
      targets_under_iff.mpr ⟨H, hvisible.1, hBH.1, hBH.2⟩⟩
  · exact Or.inr hequiv

theorem voterProcessedTarget_of_genuineConfirmation_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s B)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s B).card := by
    have heligible := hgenuine.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v s).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
          (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s B).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  have hvisible := supportingTarget_visibleAtVoteDuty_after_gst
    S adm hv hw hpost hhor hroot huBy.1 hfind hBH.2
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hHmem : H ∈ duty.T :=
    Proofs.HealingLemmas.find?_mem hvisible.1
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hHn : H ∈ (rho.stateBefore S n w).st.core.T := by
    simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hHmem
  obtain hgen | ⟨C, hCerase, i, hin, t, hacc⟩ :=
    acceptsAt_block_of_processed_erased S rho w n hHn
  · have hBgen : B = Block.genesis :=
      Block.preceq_antisymm (hgen ▸ hBH.2) (Protocol.preceq_genesis B)
    subst B
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
  · have htFreeze : t < Protocol.view_freeze S.E s :=
      HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
        S adm hw hacc (Nat.succ_le_of_lt hin)
          (publicTime_view_freeze S s) (by
            simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
              Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn, hCerase] using
              hvisible.2.1)
    have hvisibleB := Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
      S adm (show AdmittedBefore S rho w H
        (Protocol.view_freeze S.E s) from
          ⟨C, hCerase, i, t, hacc, htFreeze⟩)
      hBH.2 (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.2)⟩

#print axioms adoptionTransport_B_after_gst

end Protocol

namespace Proofs.HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
/-! ## Genuine immediate confirmations -/









/-- Restricting the frozen processed-block domain can only remove candidates. -/
private theorem recoveryHandoff_voter_candidate_tree_subset_filtered
    (E : Env V) (st : Protocol.HealingStore V) :
    Proofs.Optimistic.voter_candidate_tree E st ⊆
      Protocol.get_filtered_block_tree st.toFG := by
  intro B hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hB ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩

/-! ## Frozen candidate paths -/

private theorem recoveryHandoff_processedPath_of_frozenCandidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : Block V}
    (hB : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) :
    ∀ C : Block V, Block.Preceq C B →
      C ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hBdata := hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hBdata
  have hBprocessed : B ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := hBdata.1.1.1
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hpc : ParentClosed (NamedRun.stateBefore S rho n w).st.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBefore S rho n w
  intro C hCB
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    at hBprocessed ⊢
  rw [hslot, Nat.add_sub_cancel] at hBprocessed ⊢
  rcases hBprocessed with ⟨hBT, hstamp | ⟨P, hP, hBP⟩⟩
  · have hBTn : B ∈ (NamedRun.stateBefore S rho n w).st.core.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hBT
    have hstampn : stampedBefore
        (NamedRun.stateBefore S rho n w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) B = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hstamp
    rcases acceptsAt_block_of_processed_erased S rho w n hBTn with
      hgen | ⟨D, hDB, i, hin, t, hacc⟩
    · have hCgen : C = Block.genesis :=
        Block.preceq_antisymm (hgen ▸ hCB) (Protocol.preceq_genesis C)
      subst C
      have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
    · have htFreeze : t < Protocol.view_freeze S.E s :=
        have hstampD : stampedBefore
            (NamedRun.stateBefore S rho n w).st.core.timestamp_block
            (Protocol.view_freeze S.E s) D.erase = true := by
          simpa only [hDB] using hstampn
        HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hw hacc (Nat.succ_le_of_lt hin)
            (publicTime_view_freeze S s) hstampD
      have hvisibleC := Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
        S adm (show AdmittedBefore S rho w B
          (Protocol.view_freeze S.E s) from ⟨D, hDB, i, t, hacc, htFreeze⟩)
        hCB (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleC.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleC.2)⟩
  · have hPT : P ∈ duty.T := by
      simpa only [Protocol.Store.toHealing] using hP.1
    have hPTn : P ∈ (NamedRun.stateBefore S rho n w).st.core.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hPT
    have hCP : Block.Preceq C P := Block.preceq_trans hCB hBP
    have hCTn : C ∈ (NamedRun.stateBefore S rho n w).st.core.T :=
      Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff _).mp hpc).2 C P hPTn hCP
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hCTn,
      Or.inr ⟨P, hP, hCP⟩⟩




/-
/-- Construct the next-vote adoption interface from the target-local root,
anchor, and exact frozen candidate. The source and target only need to be
honest; no global cone, GST-zero assumption, or alignment predicate is
required. -/
theorem nextVoteAdoption_of_recovery_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {v w: V} (hv: v ∈ rho.honest) (hw: w ∈ rho.honest)
    {s: Slot} (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B: Block V}
    (hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    (hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) B)
    (hcandidate: B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing):
    Protocol.NextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s B w:= by
  have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
    exact le_trans (le_of_lt (by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos)) hhor
  let transport:= Protocol.adoptionTransport_B_after_gst
    S adm hv hw hpost hhor hroot
  refine
    { transport:= by
        simpa only [Proofs.Optimistic.voteDutyStore_slot] using transport
      support_subset:= ?_
      anchor:= ?_
      path:= fun _ C hAC hCne hCB => by
        rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
        exact recoveryHandoff_votePath_of_frozenCandidate
          S adm hw hcandidate C hAC hCne hCB
      run:= by
        have hgate: Proofs.Optimistic.StoreGateProcessedBefore S rho:= by
          intro x hx t
          exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t x).1.1.1
        let n:= NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w
        have hstate:= Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.vote_time S.E (s + 1)) w
        have hroots: Proofs.NamedStoreRoots.RootsInTree n.st:= hstate.1.1.2
        have hrootDuty:
            Protocol.get_fg_root
                (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG ∈
              (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T:= by
          have hrootPre:= Proofs.NamedStoreRoots.fg_root_mem n.st hroots
          simpa only [n, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootPre
        exact Proofs.Optimistic.voteDutyHead_runBlock S
          adm.toNamedScheduleWellFormed hgate hw (s + 1) hrootDuty
      emit:= ?_ }
  · apply Protocol.voter_support_view_subset S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).s
    obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
    intro C hC
    apply Proofs.Optimistic.carried_support_subset_of_mem_T S adm w n
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hC
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hanchor
  · intro u hu
    apply Proofs.Optimistic.emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
      (Proofs.Optimistic.publicTime_vote_time S (s + 1))
      (Proofs.Optimistic.vote_time_nonneg S.E (s + 1)) hvoteHor
    apply Proofs.Optimistic.on_tick_emit_vote_mem S w
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w)
      (s + 1) (Nat.zero_lt_succ s)
    simpa only [Proofs.Optimistic.voteDutyStore] using hu

#print axioms nextVoteAdoption_of_recovery_after_gst
 -/

def recoveryVoteRead (S : Setup V) (rho : Run V) (s : Slot) (w : V) :
    NamedNodeState V :=
  NamedActionReads.confirmationReadFrom S
    (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
    (Protocol.vote_time S.E (s + 1))

private theorem recoveryHandoff_namedVotePath_of_frozenCandidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : Block V}
    (hB : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (recoveryVoteRead S rho s w).st.core.toHealing) :
    ∀ C : Block V,
      Block.Preceq
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract (recoveryVoteRead S rho s w).cache)
          S.E S.hc (recoveryVoteRead S rho s w).st.core.toHealing
          (S.hc.round_of (recoveryVoteRead S rho s w).st.core.s)) C →
      C ≠ Protocol.get_sg_root_with
        (NamedProfile.gradeContract (recoveryVoteRead S rho s w).cache)
        S.E S.hc (recoveryVoteRead S rho s w).st.core.toHealing
        (S.hc.round_of (recoveryVoteRead S rho s w).st.core.s) →
      Block.Preceq C B →
      C ∈ Proofs.Optimistic.voter_candidate_tree S.E
        (recoveryVoteRead S rho s w).st.core.toHealing := by
  let read := recoveryVoteRead S rho s w
  let st := read.st.core
  have hBfiltered : B ∈ Protocol.get_filtered_block_tree st.toHealing.toFG :=
    recoveryHandoff_voter_candidate_tree_subset_filtered S.E st.toHealing hB
  have hpc : ParentClosed st := by
    simpa only [st, read, recoveryVoteRead] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, read, recoveryVoteRead] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hBbare : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing := by
    simpa only [read, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using hB
  have hprocessed := recoveryHandoff_processedPath_of_frozenCandidate
    S adm hw hBbare
  intro C hAC _ hCB
  have hBT : B ∈ st.T :=
    Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG hBfiltered
  have hCT : C ∈ st.T := by
    apply Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff st).mp hpc).2 C B
    · exact hBT
    · exact hCB
  have hroot : Block.Preceq (Protocol.get_fg_root st.toHealing.toFG)
      (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
        S.E S.hc st.toHealing (S.hc.round_of st.s)) := by
    exact Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s)
  have hCfiltered : C ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    apply Proofs.Records.mem_filtered_of_preceq (st := st.toHealing.toFG)
      hFJ hBfiltered hCT hCB
    exact Block.preceq_trans hroot hAC
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      st.toHealing.toFG.toSG.toGoldfishStore st.toHealing.s := by
    simpa only [read, st, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using hprocessed C hCB
  have hBdata := hB
  have hCdata := hCfiltered
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hBdata
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hCdata
  obtain ⟨W, hWprocessed, hBW, hheight⟩ := hBdata.1.2
  change C ∈ Protocol.get_filtered_block_tree_from st.toHealing.toFG
    (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.toHealing.s)
  simp only [Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact
    ⟨⟨⟨hCprocessed, hCdata.1.1.2⟩, W, hWprocessed,
      Block.preceq_trans hCB hBW, hheight⟩, hCdata.2⟩


theorem nextVoteAdoption_of_recovery_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (recoveryVoteRead S rho s w).st.core.toHealing.toFG) B)
    (hanchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (recoveryVoteRead S rho s w).cache)
        S.E S.hc (recoveryVoteRead S rho s w).st.core.toHealing
        (S.hc.round_of (recoveryVoteRead S rho s w).st.core.s)) B)
    (hcandidate : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (recoveryVoteRead S rho s w).st.core.toHealing) :
    Protocol.NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s B w := by
  let read := recoveryVoteRead S rho s w
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read, recoveryVoteRead, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_vote_time S.E (s + 1)
  have hrootBare : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B := by
    simpa only [read, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using hroot
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    exact le_trans (le_of_lt (by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos)) hhor
  let transport := Protocol.adoptionTransport_B_after_gst
    S adm hv hw hpost hhor hrootBare
  refine
    { transport := by
        simpa only [read, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
          Run.stateBeforeTime, Proofs.Optimistic.slotOf_vote_time,
          NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
          Protocol.NamedStore.setClock, hslot] using transport
      support_subset := ?_
      anchor := ?_
      path := fun _ C hAC hCne hCB => by
        rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
        exact recoveryHandoff_namedVotePath_of_frozenCandidate
          S adm hw hcandidate C hAC hCne hCB
      run := by
        let pre := NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w
        have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (Protocol.vote_time S.E (s + 1)) w).1
        have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
          simpa only [read, recoveryVoteRead, pre,
            NamedActionReads.confirmationReadFrom] using
            Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st
              (Protocol.vote_time S.E (s + 1)) hinvPre
        have hroots : Proofs.NamedStoreRoots.RootsInTree read.st := hinv.1.2
        have hrootMem : Protocol.get_fg_root read.st.core.toHealing.toFG ∈
            read.st.core.T := Proofs.NamedStoreRoots.fg_root_mem read.st hroots
        let tree := Protocol.voter_filtered_block_tree S.E read.st.core
          read.st.core.s
        let votes := Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore
          read.st.core.s
        let support := Protocol.voter_support_view S.E
          read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
        let head := Protocol.get_head_in_tree_with_layer
          (NamedProfile.gradeContract read.cache) S.E S.hc
          read.st.core.toHealing tree votes support (read.st.core.s - 1)
        have htree : tree ⊆ read.st.core.T := by
          dsimp only [tree]
          rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
          intro C hC
          simp only [Proofs.Optimistic.voter_candidate_tree,
            Protocol.get_filtered_block_tree_from,
            Protocol.viable_tree, Protocol.finalized_descendants,
            Protocol.viable, Protocol.voter_processed_block_tree,
            Finset.mem_filter, decide_eq_true_eq] at hC
          exact hC.1.1.1.1
        have hanchorMem : Protocol.get_sg_root_with
            (NamedProfile.gradeContract read.cache) S.E S.hc
            read.st.core.toHealing (S.hc.round_of read.st.core.s) ∈
              read.st.core.T := by
          exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
            S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s) hrootMem
        have hhead : head ∈ read.st.core.T := by
          dsimp only [head]
          rw [Proofs.Optimistic.get_head_in_tree_split_with]
          exact Proofs.Records.ghost_mem_of _ _ hanchorMem htree
        have hheadPre : head ∈ pre.st.core.T := by
          simpa only [read, recoveryVoteRead,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hhead
        obtain ⟨C, hChead, hCrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedScheduleWellFormed hw
            (Protocol.vote_time S.E (s + 1)) hheadPre
        simpa only [tree, votes, support, head] using ⟨C, hChead, hCrun⟩
      emit := ?_ }
  · apply Protocol.voter_support_view_subset S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
    intro C hC
    apply Proofs.Optimistic.carried_support_subset_of_mem_T S adm w n
    simpa only [read, recoveryVoteRead, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hC
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hanchor
  · intro u
    dsimp only
    intro hu
    apply Proofs.Optimistic.emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
      (Proofs.Optimistic.publicTime_vote_time S (s + 1))
      (Proofs.Optimistic.vote_time_nonneg S.E (s + 1)) hvoteHor
    apply Proofs.Optimistic.on_tick_emit_vote_mem S w
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w)
      (s + 1) (Nat.zero_lt_succ s)
    simpa only [read, recoveryVoteRead] using hu

#print axioms nextVoteAdoption_of_recovery_after_gst



/-- **The prepared next-vote adoption record at COMPATIBILITY strength**
( gs, deliverable 4).

Additive twin of `nextVoteAdoption_of_recovery_after_gst`; that theorem and its
consumers are untouched. The record's own `anchor` field is compatibility
(`AdoptionRun.lean:84`), and the `Preceq` form of the hypothesis is read at
exactly one place in the proof, the line that discharges that field; the `path`
field ignores its own `Preceq` premise. So the stronger input was never needed,
and this twin is the same proof with that one line changed.

earlier builds the record the same way, from compatibility:
`nextVoteAdoption_of_commonHead_after_SG_healing`
(`PostSafetyHandoffRun.lean:34`) passes
`nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing` straight
into the `anchor` field. The named compatibility producer
`nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named`
(`SGLifetimeNamedRun.lean:984`) is live and general-slot, so compatibility is
the form its consumers can actually supply. -/
theorem nextVoteAdoption_of_recovery_after_gst_compatibleAnchor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (recoveryVoteRead S rho s w).st.core.toHealing.toFG) B)
    (hanchor : Block.compatible
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (recoveryVoteRead S rho s w).cache)
        S.E S.hc (recoveryVoteRead S rho s w).st.core.toHealing
        (S.hc.round_of (recoveryVoteRead S rho s w).st.core.s)) B = true)
    (hcandidate : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (recoveryVoteRead S rho s w).st.core.toHealing) :
    Protocol.NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s B w := by
  let read := recoveryVoteRead S rho s w
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read, recoveryVoteRead, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_vote_time S.E (s + 1)
  have hrootBare : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B := by
    simpa only [read, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using hroot
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    exact le_trans (le_of_lt (by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos)) hhor
  let transport := Protocol.adoptionTransport_B_after_gst
    S adm hv hw hpost hhor hrootBare
  refine
    { transport := by
        simpa only [read, recoveryVoteRead, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime,
          Run.stateBeforeTime, Proofs.Optimistic.slotOf_vote_time,
          NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
          Protocol.NamedStore.setClock, hslot] using transport
      support_subset := ?_
      anchor := ?_
      path := fun _ C hAC hCne hCB => by
        rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
        exact recoveryHandoff_namedVotePath_of_frozenCandidate
          S adm hw hcandidate C hAC hCne hCB
      run := by
        let pre := NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w
        have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (Protocol.vote_time S.E (s + 1)) w).1
        have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
          simpa only [read, recoveryVoteRead, pre,
            NamedActionReads.confirmationReadFrom] using
            Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st
              (Protocol.vote_time S.E (s + 1)) hinvPre
        have hroots : Proofs.NamedStoreRoots.RootsInTree read.st := hinv.1.2
        have hrootMem : Protocol.get_fg_root read.st.core.toHealing.toFG ∈
            read.st.core.T := Proofs.NamedStoreRoots.fg_root_mem read.st hroots
        let tree := Protocol.voter_filtered_block_tree S.E read.st.core
          read.st.core.s
        let votes := Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore
          read.st.core.s
        let support := Protocol.voter_support_view S.E
          read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
        let head := Protocol.get_head_in_tree_with_layer
          (NamedProfile.gradeContract read.cache) S.E S.hc
          read.st.core.toHealing tree votes support (read.st.core.s - 1)
        have htree : tree ⊆ read.st.core.T := by
          dsimp only [tree]
          rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
          intro C hC
          simp only [Proofs.Optimistic.voter_candidate_tree,
            Protocol.get_filtered_block_tree_from,
            Protocol.viable_tree, Protocol.finalized_descendants,
            Protocol.viable, Protocol.voter_processed_block_tree,
            Finset.mem_filter, decide_eq_true_eq] at hC
          exact hC.1.1.1.1
        have hanchorMem : Protocol.get_sg_root_with
            (NamedProfile.gradeContract read.cache) S.E S.hc
            read.st.core.toHealing (S.hc.round_of read.st.core.s) ∈
              read.st.core.T := by
          exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
            S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s) hrootMem
        have hhead : head ∈ read.st.core.T := by
          dsimp only [head]
          rw [Proofs.Optimistic.get_head_in_tree_split_with]
          exact Proofs.Records.ghost_mem_of _ _ hanchorMem htree
        have hheadPre : head ∈ pre.st.core.T := by
          simpa only [read, recoveryVoteRead,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hhead
        obtain ⟨C, hChead, hCrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedScheduleWellFormed hw
            (Protocol.vote_time S.E (s + 1)) hheadPre
        simpa only [tree, votes, support, head] using ⟨C, hChead, hCrun⟩
      emit := ?_ }
  · apply Protocol.voter_support_view_subset S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
    intro C hC
    apply Proofs.Optimistic.carried_support_subset_of_mem_T S adm w n
    simpa only [read, recoveryVoteRead, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hC
  · exact hanchor
  · intro u
    dsimp only
    intro hu
    apply Proofs.Optimistic.emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
      (Proofs.Optimistic.publicTime_vote_time S (s + 1))
      (Proofs.Optimistic.vote_time_nonneg S.E (s + 1)) hvoteHor
    apply Proofs.Optimistic.on_tick_emit_vote_mem S w
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w)
      (s + 1) (Nat.zero_lt_succ s)
    simpa only [read, recoveryVoteRead] using hu

#print axioms nextVoteAdoption_of_recovery_after_gst_compatibleAnchor






#print axioms voterCandidate_of_processed_self_and_filtered

end Proofs.HealingSurface
end DecoupledConsensusModel

end
