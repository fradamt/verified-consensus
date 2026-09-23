module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4LatestFinalizedCompatibilityClosed
public import DecoupledConsensusProofs.Execution.PreparedV4LiveMonotoneClosed
public import DecoupledConsensusProofs.Execution.PreparedV4VoteSourcesClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedV4CanonicalProposalDuty
public import DecoupledConsensusProofs.Protocol.ChainState.WholeRunFinalitySafety
public import DecoupledConsensusProofs.Protocol.Handlers.UserConfirmationRecovery
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmedOutput

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Phase-shift safety from a prepared V4 bootstrap -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_confirmation_mono
    (S : Setup V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time S.E s ≤ Protocol.confirmation_time S.E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono S.E (Nat.add_le_add_right hst 1)

private theorem preparedV4_confirmation_strict
    (S : Setup V) {s t : Slot} (hst : s < t) :
    Protocol.confirmation_time S.E s < Protocol.confirmation_time S.E t := by
  have hnext : Protocol.confirmation_time S.E s <
      Protocol.confirmation_time S.E (s + 1) :=
    (confirmation_time_lt_proposal_time_of_add_two_le S.E
      (Nat.le_refl (s + 2))).trans
        (proposal_time_succ_lt_confirmation_time S.E (s + 1))
  exact hnext.trans_le
    (preparedV4_confirmation_mono S (Nat.succ_le_of_lt hst))

private theorem preparedV4_confirmation_max
    (S : Setup V) {rho : Run V} (s t : Slot)
    (hs : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (ht : Protocol.confirmation_time S.E t ≤ rho.horizon) :
    Protocol.confirmation_time S.E (max s t) ≤ rho.horizon := by
  rcases le_total s t with h | h
  · simpa only [max_eq_right h] using ht
  · simpa only [max_eq_left h] using hs

private theorem preparedV4_voteTime_lt_nextProposal
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ E s)
  rw [← vote_time_add_delta]
  exact Int.lt_add_of_pos_right _ E.Δ_pos

private theorem preparedV4_storeBeforeTime_eq_storeAt_sub_one
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    rho.storeBeforeTime S v t = rho.storeAt S v (t - 1) := by
  have hfilter : rho.events.filter (fun e : Event V => decide (e.time < t)) =
      rho.events.filter (fun e : Event V => decide (e.time ≤ t - 1)) := by
    apply List.filter_congr
    intro e _
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  unfold Run.storeBeforeTime Run.storeAt NamedRun.stateBeforeTime NamedRun.readAt
  rw [hfilter]

private theorem preparedV4_liveField_preceq_at_prefix_of_suffixSelections
    (S : Setup V) (rho : Run V) (v : V) (B : Block V) {m : Nat}
    (hbase : Block.Preceq
      (rho.stateBefore S m v).st.live_confirmed B) :
    ∀ n, m ≤ n →
      (∀ i C, m ≤ i → i < n →
        ConfirmationSelectionAt S rho v i C → Block.Preceq C B) →
      Block.Preceq (rho.stateBefore S n v).st.live_confirmed B := by
  intro n
  induction n with
  | zero =>
      intro hm _
      simpa only [Nat.le_zero.mp hm] using hbase
  | succ n ih =>
      intro hm hprior
      by_cases heq : m = n + 1
      · simpa only [← heq] using hbase
      have hmn : m ≤ n := by omega
      have hIH := ih hmn (fun i C hmi hin hsel =>
        hprior i C hmi (Nat.lt_succ_of_lt hin) hsel)
      change Block.Preceq
        (NamedRun.stateBefore S rho (n + 1) v).st.live_confirmed B
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases hn : rho.events[n]? with
      | none => simpa using hIH
      | some e =>
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o time =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                rw [Proofs.Optimistic.process_live_confirmed]
                exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH
          | tick u time =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                by_cases hbranch : 0 < S.E.slotOf time ∧
                    time = Protocol.support_cutoff S.E (S.E.slotOf time)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have hout := Proofs.Optimistic.on_tick_emit_confirmation
                    S v (rho.stateBefore S n v) (S.E.slotOf time) hpos
                  rw [← ht] at hout
                  rw [hout]
                  exact hprior n _ hmn (Nat.lt_succ_self n)
                    ⟨time, hn, hpos, ht, rfl⟩
                · rw [Proofs.Optimistic.on_tick_emit_live_confirmed_of_ne
                    S v (rho.stateBefore S n v) time hbranch]
                  exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH

/-- The public vote-source record protects every actual stored live value,
using the same suffix-origin fold as `ActualVoteSafety.live_at_read`. -/
private theorem VoteSourcesSafeAt.live_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cut : Round} {d : Slot} {P : Block V}
    (hsafe : VoteSourcesSafeAt S rho cut d P)
    {t : Time} (htHor : t ≤ rho.horizon)
    (hlo : Protocol.confirmation_time S.E (S.hc.opening_slot cut) ≤ t)
    (hhi : t < Protocol.confirmation_time S.E d)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (voterHeadAt S rho x d) := by
  let q0 := S.hc.opening_slot cut
  have hq0d : q0 < d := by
    by_contra h
    exact (not_lt_of_ge
      (preparedV4_confirmation_mono S (Nat.le_of_not_gt h)))
      (hlo.trans_lt hhi)
  have hq0Hor : Protocol.confirmation_time S.E q0 ≤ rho.horizon :=
    hlo.trans htHor
  let m := (rho.events.filter (fun e =>
    decide (e.time ≤ Protocol.confirmation_time S.E q0))).length
  have hbase : Block.Preceq (rho.stateBefore S m v).st.live_confirmed
      (voterHeadAt S rho x d) := by
    have h := hsafe.live q0 (le_refl _) hq0d hq0Hor v hv x hx
    simpa only [Run.storeAt,
      stateAt_eq_take S adm.toNamedScheduleWellFormed, m] using h
  rw [Run.storeAt, stateAt_eq_take S adm.toNamedScheduleWellFormed]
  apply preparedV4_liveField_preceq_at_prefix_of_suffixSelections
    S rho v _ hbase _ (filter_le_length_mono rho hlo)
  intro i C hmi hin hsel
  obtain ⟨q, hqevent, hC, hqHor⟩ :=
    confirmationSelectionAt_slot_core S adm hsel
  have hCprepared :
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).cache)
        S.E S.hc (confStore S rho v q) q).live_confirmed = C := by
    rw [Proofs.Optimistic.confStore_eq_confirmationInputRead]
    change (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).cache)
      S.E S.hc
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).st q).core.live_confirmed = C
    simpa only [confirmationWrite,
      Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel,
      Protocol.NamedStore.live_confirmed,
      Protocol.NamedDuties.update_confirmation_with] using hC
  have hqBefore : Protocol.confirmation_time S.E q <
      Protocol.confirmation_time S.E d := by
    have h := filter_true_of_index_lt S adm.toNamedScheduleWellFormed _
      (downward_le t) hin hqevent
    exact (of_decide_eq_true h).trans_lt hhi
  have hqAfter : Protocol.confirmation_time S.E q0 <
      Protocol.confirmation_time S.E q := by
    have h := filter_false_of_index_ge S adm.toNamedScheduleWellFormed _
      (downward_le (Protocol.confirmation_time S.E q0)) hmi hqevent
    simpa only [decide_eq_false_iff_not, not_le, Event.time] using h
  have hqlo : q0 ≤ q := by
    by_contra h
    exact (not_lt_of_ge
      (preparedV4_confirmation_mono S (Nat.le_of_lt (Nat.lt_of_not_ge h))))
      hqAfter
  have hqhi : q < d := by
    by_contra h
    exact (not_lt_of_ge
      (preparedV4_confirmation_mono S (Nat.le_of_not_gt h))) hqBefore
  have hsel' := hsafe.live q hqlo hqhi hqHor v hv x hx
  rw [live_confirmed_eq_update
    S adm.toNamedScheduleWellFormed hv q hqHor] at hsel'
  rw [← hCprepared]
  exact hsel'

/-- Refreshed latest-record safety follows from the two available common-head
bounds. It does not use the opening latest seed. -/
private theorem SettledBootstrapPreparedV4.refreshedLatestSafety_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon) :
    RefreshedLatestSafety S rho (base + S.hc.η_SG) start := by
  have hcutTime (q : Slot)
      (hq : S.hc.opening_slot (base + S.hc.η_SG) ≤ q) :
      Protocol.confirmation_time S.E
          (S.hc.opening_slot (base + S.hc.η_SG)) ≤
        Protocol.confirmation_time S.E q :=
    preparedV4_confirmation_mono S hq
  constructor
  · intro u hu v hv t t' ht ht' hleft hright
    obtain ⟨x, hx, q, hq, hqHor, hleftEq⟩ := hleft
    obtain ⟨y, hy, p, hp, hpHor, hrightEq⟩ := hright
    let last := max start (max q p)
    have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon :=
      preparedV4_confirmation_max S start (max q p) hstartHor
        (preparedV4_confirmation_max S q p hqHor hpHor)
    have hstart : start ≤ last + 1 :=
      (Nat.le_max_left start (max q p)).trans (Nat.le_succ last)
    have hqLast : q < last + 1 := Nat.lt_succ_of_le
      ((Nat.le_max_left q p).trans (Nat.le_max_right start (max q p)))
    have hpLast : p < last + 1 := Nat.lt_succ_of_le
      ((Nat.le_max_right q p).trans (Nat.le_max_right start (max q p)))
    have hqHead :=
      SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hlastHor hstart (le_refl _)
          (hcutTime q hq) (preparedV4_confirmation_strict S hqLast) hx hu
    have hpHead :=
      SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hlastHor hstart (le_refl _)
          (hcutTime p hp) (preparedV4_confirmation_strict S hpLast) hy hu
    rw [hleftEq, hrightEq]
    exact Block.compatible_of_preceq_common hqHead hpHead
  · intro u hu v hv t ht htHor hselected
    obtain ⟨w, hw, q, hq, hqHor, hselectedEq⟩ := hselected
    let first := max start q
    have hfirstHor : Protocol.confirmation_time S.E first ≤ rho.horizon :=
      preparedV4_confirmation_max S start q hstartHor hqHor
    have hstart : start ≤ first + 1 :=
      (Nat.le_max_left start q).trans (Nat.le_succ first)
    have hread : min (S.a (base + S.hc.η_SG))
        (Protocol.vote_time S.E start) ≤ t :=
      (min_le_right _ _).trans
        ((vote_time_le_confirmation_time S.E start).trans ht)
    obtain ⟨last, hfirstLast, hlastHor, hroot⟩ :=
      SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core
        S adm hcom hboot hawake hfinality hfirstHor hstart hread hv hu
    have hqLast : q < last + 1 := Nat.lt_succ_of_le
      ((Nat.le_max_right start q).trans hfirstLast)
    have hstartLast : start ≤ last + 1 :=
      (Nat.le_max_left start q).trans
        (hfirstLast.trans (Nat.le_succ last))
    have hqHead :=
      SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hlastHor hstartLast (le_refl _)
          (hcutTime q hq) (preparedV4_confirmation_strict S hqLast) hw hu
    rw [hselectedEq]
    exact Block.compatible_of_preceq_common hqHead hroot

private theorem SettledBootstrapPreparedV4.latestCompatible_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon) :
    ConfirmationCompatibleFrom S rho
      (Protocol.confirmation_time S.E start) := by
  intro u hu v hv t t' ht ht' htHor htHor'
  obtain ⟨a, haStart, haHor, ha⟩ :=
    SettledBootstrapPreparedV4.latest_has_voteHead_bound_core
      S adm hcom hboot hlatest hawake hfinality hstartHor hu ht
  obtain ⟨b, hbStart, hbHor, hb⟩ :=
    SettledBootstrapPreparedV4.latest_has_voteHead_bound_core
      S adm hcom hboot hlatest hawake hfinality hstartHor hv ht'
  have hmaxHor : Protocol.confirmation_time S.E (max a b) ≤ rho.horizon :=
    preparedV4_confirmation_max S a b haHor hbHor
  exact Block.compatible_of_preceq_common
    (ha (max a b) (Nat.le_max_left _ _) hmaxHor u hu)
    (hb (max a b) (Nat.le_max_right _ _) hmaxHor u hu)

private theorem SettledBootstrapPreparedV4.headExtendsStable_at_seed_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq
      (confirmationStableWrite S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v start))
      (Protocol.advance_confirmed
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v start).st.core.latest_confirmed
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v start) start)) := by
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho v start
  let contract := NamedProfile.gradeContract read.cache
  let updated := Protocol.update_confirmation_with contract S.E S.hc
    (confStore S rho v start) start
  have hstable : Block.Preceq (confirmationStableWrite S read) P.erase := by
    have h := ConfirmationOrigin.update_confirmation_stable_le_confirmed
      contract S.E S.hc read.st start
    have h' : Block.Preceq updated.latest_stable updated.latest_confirmed := by
      simpa only [read, contract, updated,
        Protocol.NamedDuties.update_confirmation_with,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using h
    rw [hlatest v hv] at h'
    simpa only [read, contract, updated, confirmationStableWrite,
      Protocol.NamedDuties.update_confirmation_with,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using h'
  have hg := SettledBootstrapPreparedV4.genuineConfirmationAt_core
    S adm hcom hboot hawake hfinality (le_refl start) hstartHor hv
  have hwalk : updated.live_confirmed = namedConfirmationWalk S read start := by
    rw [Protocol.update_confirmation_with_live_confirmed,
      if_pos (by simpa only [read] using hg.2)]
    rfl
  have hPwalk : P.erase = namedConfirmationWalk S read start :=
    (hboot.confirmationSeedPrepared v hv).symm.trans hwalk
  exact Block.preceq_trans (hPwalk ▸ hstable)
    (Proofs.ConfirmationPolicy.candidate_preceq_advance _ _)

private theorem SettledBootstrapPreparedV4.latest_compatible_walk_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hstarts : start < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    Block.compatible
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed
      (namedConfirmationWalk S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) = true := by
  have hstartLt := preparedV4_confirmation_strict S hstarts
  have hpredLo : Protocol.confirmation_time S.E start ≤
      Protocol.confirmation_time S.E s - 1 :=
    Int.le_sub_one_iff.mpr hstartLt
  obtain ⟨a, haStart, haHor, ha⟩ :=
    SettledBootstrapPreparedV4.latest_has_voteHead_bound_core
      S adm hcom hboot hlatest hawake hfinality hstartHor hv hpredLo
  let last := max a s
  have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon :=
    preparedV4_confirmation_max S a s haHor hhor
  have hstartLast : start ≤ last + 1 :=
    hstarts.le.trans ((Nat.le_max_right a s).trans (Nat.le_succ last))
  have hsLast : s < last + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right a s)
  have hcutTime : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤
      Protocol.confirmation_time S.E s :=
    preparedV4_confirmation_mono S (hboot.settled.trans hstarts.le)
  have hwalkHead :=
    SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
      S adm hcom hboot hawake hfinality hlastHor hstartLast (le_refl _)
        hcutTime (preparedV4_confirmation_strict S hsLast) hv hv
  have hg := SettledBootstrapPreparedV4.genuineConfirmationAt_core
    S adm hcom hboot hawake hfinality hstarts.le hhor hv
  have hlatestHead := ha last (Nat.le_max_left _ _) hlastHor v hv
  rw [← preparedV4_storeBeforeTime_eq_storeAt_sub_one S rho v
    (Protocol.confirmation_time S.E s)] at hlatestHead
  rw [hg.1] at hwalkHead
  exact Block.compatible_of_preceq_common hlatestHead hwalkHead

private theorem SettledBootstrapPreparedV4.headExtendsStable_after_start_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hstarts : start < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    Block.Preceq
      (confirmationStableWrite S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s))
      (Protocol.advance_confirmed
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s)) := by
  have hnest : Block.Preceq
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_stable
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_confirmed := by
    let t := Protocol.confirmation_time S.E s
    let n := (rho.events.filter (fun e => decide (e.time < t))).length
    have hstate : NamedRun.stateBeforeTime S rho t v =
        NamedRun.stateBefore S rho n v := by
      simpa only [Run.stateBeforeTime, Run.stateBefore, n, t] using
        congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
          S adm.toNamedScheduleWellFormed t) v
    unfold Internal.NamedRecoveryRead.confirmationInputRead
      NamedActionReads.confirmationReadAt
      NamedActionReads.confirmationReadFrom
    rw [hstate]
    exact ConfirmationOrigin.stateBefore_stable_below_confirmed S rho v n
  have hcompat := SettledBootstrapPreparedV4.latest_compatible_walk_core
    S adm hcom hboot hlatest hawake hfinality hstartHor hv hstarts hhor
  have hnew :
      confirmationStableWrite S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) =
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_stable ∨
      Block.Preceq
        (confirmationStableWrite S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s))
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) := by
    unfold confirmationStableWrite
    cases hroot : (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache).stableRoot
        S.E S.hc
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.toHealing
        (S.hc.round_of
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.s) with
    | none => exact Or.inl rfl
    | some G =>
        dsimp only
        rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.latest_stable
          G with hkeep | hwrite
        · exact Or.inl hkeep
        · refine Or.inr ?_
          rw [hwrite]
          let t := Protocol.confirmation_time S.E s
          let r := S.hc.round_of (S.E.slotOf t)
          have hcutPos : 0 < base + S.hc.η_SG :=
            Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
          have hRleStart : S.hc.R ≤ start := by
            calc
              S.hc.R = 1 * S.hc.R := by omega
              _ ≤ (base + S.hc.η_SG) * S.hc.R :=
                Nat.mul_le_mul_right S.hc.R (Nat.succ_le_iff.mpr hcutPos)
              _ ≤ start := hboot.settled
          have hRle : S.hc.R ≤ S.E.slotOf t := by
            simp only [t, slotOf_confirmation_time]
            exact hRleStart.trans (hstarts.le.trans (Nat.le_succ s))
          have hr : 0 < r :=
            Nat.div_pos hRle
              (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
          have ht0 : (0 : Time) ≤ t :=
            Proofs.Optimistic.confirmation_time_nonneg S.E s
          have hcut : t = Protocol.support_cutoff S.E (S.E.slotOf t) := by
            dsimp only [t]
            rw [Proofs.Optimistic.slotOf_confirmation_time]
            exact Protocol.confirmation_time_eq_support_cutoff_succ S.E s
          have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r < t :=
            NamedOutageClosure.opening_lt_support_cutoff S t ht0 hcut
          have htop : t ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
            simpa only [r, NamedOutageClosure.clockRoundAt] using
              (NamedOutageClosure.clockRound_lt_opening_succ S t).le
          apply WeakGenesis.preparedStableRoot_preceq_confWalk_positive
            S adm hv hr
              (rfl : S.hc.round_of (S.E.slotOf t) = r)
              hopen htop (by simpa only [t] using hhor) s
          simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
            NamedActionReads.confirmationReadAt, t, r,
            slotOf_confirmation_time,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hroot
  exact StableRecord.preceq_advance_of_nesting hnew hnest hcompat

private theorem SettledBootstrapPreparedV4.honestHeadExtendsStable_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon) :
    HonestHeadExtendsStableFrom S rho
      (Protocol.confirmation_time S.E start) := by
  intro v hv s hs hhor
  have hslots : start ≤ s := by
    by_contra hnot
    have hlt : s < start := Nat.lt_of_not_ge hnot
    exact (not_lt_of_ge hs) (preparedV4_confirmation_strict S hlt)
  rcases hslots.eq_or_lt with rfl | hlt
  · exact SettledBootstrapPreparedV4.headExtendsStable_at_seed_core
      S adm hcom hboot hlatest hawake hfinality hstartHor hv
  · exact SettledBootstrapPreparedV4.headExtendsStable_after_start_core
      S adm hcom hboot hlatest hawake hfinality hstartHor hv hlt hhor

/-- All phase-shift fields except proposal-read reorganization assemble from
the closed prepared V4 producers. The callback is the exact field statement. -/
private theorem SettledBootstrapPreparedV4.phaseShiftSafety_core_of_reads
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (hsb : SlashableBound S rho)
    (hproposalReads : ∀ s, start < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s) :
    PhaseShiftSafety S rho (base + S.hc.η_SG) start P.erase := by
  have hwhole := wholeRunFinalitySafety_of_slashableBound S adm hsb
  have hcompat := SettledBootstrapPreparedV4.latestCompatible_core
    S adm hcom hboot hlatest hawake hfinality hstartHor
  have hmono := confirmationMonotoneFrom S adm.toNamedScheduleWellFormed
    (Protocol.confirmation_time S.E start) hcompat
  have hcross : ∀ {v w : V}, v ∈ rho.honest → w ∈ rho.honest →
      ∀ {t u : Time}, Protocol.confirmation_time S.E start ≤ t →
      Protocol.confirmation_time S.E start ≤ u → t ≤ rho.horizon →
      u ≤ rho.horizon → Block.compatible
        (rho.storeAt S v t).core.latest_confirmed
        (rho.storeAt S w u).core.F = true := by
    intro v w hv hw t u ht hu htHor huHor
    exact SettledBootstrapPreparedV4.latest_compatible_finalized_core
      S adm hcom hboot hlatest hawake hfinality hstartHor
        hv hw ht hu htHor huHor
  have houtputCompatible : ConfirmedOutputCompatibleFrom S rho
      (Protocol.confirmation_time S.E start) := by
    apply ConfirmedOutput.confirmedOutputCompatibleFrom_of_fields
      S hwhole hcompat
    · intro w hw t ht htHor
      exact StableRecord.stableBelowConfirmed_storeAt
        S adm.toNamedScheduleWellFormed w t
    intro v hv w hw t u ht hu htHor huHor
    exact Protocol.compatible_comm (hcross hw hv hu ht huHor htHor)
  have houtputMonotone : ConfirmedOutputMonotoneFrom S rho
      (Protocol.confirmation_time S.E start) := by
    apply ConfirmedOutput.confirmedOutputMonotoneFrom_of_cross
      S adm.toNamedScheduleWellFormed hmono
    · intro w hw t ht htHor
      exact StableRecord.stableBelowConfirmed_storeAt
        S adm.toNamedScheduleWellFormed w t
    intro v hv t u ht htu huHor
    exact hcross hv hv ht (ht.trans htu) (htu.trans huHor) huHor
  have hheads := SettledBootstrapPreparedV4.honestHeadExtendsStable_core
    S adm hcom hboot hlatest hawake hfinality hstartHor
  have hproposals : UserProposalsConfirmedAfter S rho start := by
    intro s hs hhor hprop
    have hpHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
      (proposal_time_le_confirmation_time S.E s).trans hhor
    obtain ⟨B, hB, -, -⟩ := proposedBlockAt_emits_of_honest
      S adm.toNamedScheduleWellFormed s
        ((Nat.zero_le start).trans_lt hs) hprop hpHor
    have hduty := SettledBootstrapPreparedV4.canonicalProposalDuty_core
      S adm hcom hboot hawake hfinality hs hhor hprop hB
    have hafter := preparedV4_confirmation_mono S hs.le
    have hat : ∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed =
          B.erase := by
      intro v hv
      exact UserConfirmationFreshness.latest_eq_proposedBlock_of_duty
        S adm hheads hcom hB hduty hafter hhor hv
    refine ⟨B, hB, hat, ?_⟩
    intro v hv t ht htHor
    have hpre := hmono v hv (Protocol.confirmation_time S.E s) t
      hafter ht htHor
    rw [hat v hv] at hpre
    have hcompatFinal := hcross hv hv hafter (hafter.trans ht) hhor htHor
    change Block.compatible
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed
      (rho.storeAt S v t).F = true at hcompatFinal
    rw [hat v hv] at hcompatFinal
    exact ConfirmedOutput.preceq_get_confirmed_of_latest _
      (StableRecord.stableBelowConfirmed_storeAt
        S adm.toNamedScheduleWellFormed v t) hpre hcompatFinal
  have huser : UserConfirmationAfterHealing S rho start P.erase := by
    have hat : ∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E start)).latest_confirmed =
          P.erase := by
      intro v hv
      rw [latest_confirmed_eq_update
        S adm.toNamedScheduleWellFormed hv start hstartHor]
      exact hlatest v hv
    refine ⟨hat, hcompat, hmono, houtputCompatible,
      houtputMonotone, hproposals, ?_⟩
    intro v hv t ht htHor
    have hpre := hmono v hv (Protocol.confirmation_time S.E start) t
      (le_refl _) ht htHor
    rw [hat v hv] at hpre
    have hcompatFinal := hcross hv hv (le_refl _) ht hstartHor htHor
    change Block.compatible
      (rho.storeAt S v (Protocol.confirmation_time S.E start)).latest_confirmed
      (rho.storeAt S v t).F = true at hcompatFinal
    rw [hat v hv] at hcompatFinal
    exact ConfirmedOutput.preceq_get_confirmed_of_latest _
      (StableRecord.stableBelowConfirmed_storeAt
        S adm.toNamedScheduleWellFormed v t) hpre hcompatFinal
  have hrefreshed := SettledBootstrapPreparedV4.refreshedLatestSafety_core
    S adm hcom hboot hawake hfinality hstartHor
  refine
    { finality := hwhole
      userConfirmation := huser
      refreshedLatest := hrefreshed
      liveMonotone := ?_
      liveCompatible := ?_
      genuine := ?_
      liveAtConfirmation := ?_
      seedAtVote := ?_
      liveAtVote := ?_
      honestProposalLive := ?_
      honestProposalReads := hproposalReads }
  · intro v hv t u ht htu
    exact SettledBootstrapPreparedV4.liveConfirmed_mono_core
      S adm hcom hboot hawake hfinality hv ht htu
  · intro last hlastHor hstart t u ht hu htLast huLast v hv w hw
    have hnext : Protocol.confirmation_time S.E last <
        Protocol.confirmation_time S.E (last + 1) :=
      preparedV4_confirmation_strict S (Nat.lt_succ_self last)
    have hcutTime : Protocol.confirmation_time S.E
        (S.hc.opening_slot (base + S.hc.η_SG)) =
        S.a (base + S.hc.η_SG) := opening_confirmation_time_eq_action S _
    exact Block.compatible_of_preceq_common
      (SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hlastHor hstart (le_refl _)
          (hcutTime.symm ▸ ht) (htLast.trans_lt hnext) hv hv)
      (SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hlastHor hstart (le_refl _)
          (hcutTime.symm ▸ hu) (huLast.trans_lt hnext) hw hv)
  · intro s hs hhor v hv
    exact SettledBootstrapPreparedV4.genuineConfirmationAt_core
      S adm hcom hboot hawake hfinality hs hhor hv
  · intro s hs hhor u hu v hv t hlo hhi
    have hcutTime : Protocol.confirmation_time S.E
        (S.hc.opening_slot (base + S.hc.η_SG)) =
        S.a (base + S.hc.η_SG) := opening_confirmation_time_eq_action S _
    exact SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core
      S adm hcom hboot hawake hfinality hs hhor hv hu
        (hcutTime.symm ▸ hlo) hhi
  · intro d hd hhor v hv
    exact (SettledBootstrapPreparedV4.voteSourcesSafeAt_core
      S adm hcom hboot hawake hfinality hd hhor).seed v hv
  · intro d hd hhor u hu v hv t hlo htHor hhi
    have hcutTime : Protocol.confirmation_time S.E
        (S.hc.opening_slot (base + S.hc.η_SG)) =
        S.a (base + S.hc.η_SG) := opening_confirmation_time_eq_action S _
    exact VoteSourcesSafeAt.live_at_read S adm
      (SettledBootstrapPreparedV4.voteSourcesSafeAt_core
        S adm hcom hboot hawake hfinality hd hhor)
      htHor (hcutTime.symm ▸ hlo) hhi hu hv
  · intro s hs hhor hprop
    have hpHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
      (proposal_time_le_confirmation_time S.E s).trans hhor
    obtain ⟨B, hB, -, -⟩ := proposedBlockAt_emits_of_honest
      S adm.toNamedScheduleWellFormed s
        ((Nat.zero_le start).trans_lt hs) hprop hpHor
    exact ⟨B, hB, fun v hv =>
      SettledBootstrapPreparedV4.honestProposal_liveConfirmed_core
        S adm hcom hboot hawake hfinality hs hhor hprop hB hv⟩

private theorem preparedV4_protectedVoteSlot_of_heads
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x d)) :
    ProtectedVoteSlot S rho d B := by
  refine ⟨hheads, ?_⟩
  intro x hx hcommittee
  obtain ⟨X, hX, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx hd hcommittee hhor
  exact ⟨X, by simpa only [hX] using hheads x hx, hXrun, hXemit⟩

private theorem SettledBootstrapPreparedV4.honestProposal_preceq_voterHeadAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s k : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hs : start < s)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hsk : s ≤ k) (hhor : Protocol.vote_time S.E k ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq B.erase (voterHeadAt S rho v k) := by
  rcases hsk.eq_or_lt with rfl | hlt
  · cases s with
    | zero => exact False.elim ((Nat.not_lt_zero start) hs)
    | succ d =>
        rw [SettledBootstrapPreparedV4.honestProposal_voterHeadAt_eq_core
          S adm hcom hboot hawake hfinality (Nat.le_of_lt_succ hs)
            hsourceHor hprop hB v hv]
        exact Block.preceq_self _
  · have hsafe := SettledBootstrapPreparedV4.voteSourcesSafeAt_core
      S adm hcom hboot hawake hfinality (hs.le.trans hlt.le) hhor
    have hlive := SettledBootstrapPreparedV4.honestProposal_liveConfirmed_core
      S adm hcom hboot hawake hfinality hs hsourceHor hprop hB hv
    have h := hsafe.live s (hboot.settled.trans hs.le) hlt
      hsourceHor v hv v hv
    rwa [hlive] at h

/-- The prepared V4 bootstrap supplies every public phase-shift safety field
from the latest opening seed. -/
theorem SettledBootstrapPreparedV4.phaseShiftSafety_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (hsb : SlashableBound S rho) :
    PhaseShiftSafety S rho (base + S.hc.η_SG) start P.erase := by
  apply SettledBootstrapPreparedV4.phaseShiftSafety_core_of_reads
    S adm hcom hboot hlatest hawake hfinality hstartHor hsb
  intro s hs hsourceHor hprop
  constructor
  · intro B hB k hsk hhor hkprop
    cases k with
    | zero => exact False.elim ((Nat.not_lt_zero s) hsk)
    | succ d =>
        have hsd : s ≤ d := Nat.le_of_lt_succ hsk
        have hspos : 0 < s := (Nat.zero_le start).trans_lt hs
        have hdpos : 0 < d := hspos.trans_le hsd
        have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
          (preparedV4_voteTime_lt_nextProposal S.E d).le.trans hhor
        have hheads : ∀ x ∈ rho.honest,
            Block.Preceq B.erase (voterHeadAt S rho x d) := by
          intro x hx
          exact SettledBootstrapPreparedV4.honestProposal_preceq_voterHeadAt_core
            S adm hcom hboot hawake hfinality hs hsourceHor hprop hB
              hsd hvoteHor hx
        have hprotected := preparedV4_protectedVoteSlot_of_heads
          S adm hdpos hvoteHor hheads
        have hlastHor : Protocol.confirmation_time S.E (d - 1) ≤
            rho.horizon := by
          rw [Protocol.confirmation_time_eq_support_cutoff_succ,
            Nat.sub_add_cancel hdpos]
          exact (support_cutoff_le_proposal_time_succ S.E d).trans hhor
        have hupper : d ≤ d - 1 + 1 := by
          rw [Nat.sub_add_cancel hdpos]
        simpa only [proposerHeadAt] using
          SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
            S adm hcom hboot hawake hfinality hlastHor
              (hs.le.trans hsd) hupper hhor hkprop hprotected
  · intro B hB k hsk hhor v hv
    exact SettledBootstrapPreparedV4.honestProposal_preceq_voterHeadAt_core
      S adm hcom hboot hawake hfinality hs hsourceHor hprop hB hsk hhor hv
  · intro B hB r hsr hhor v hv
    let d := S.hc.opening_slot r + 1
    have hvoteCut : Protocol.vote_time S.E d ≤
        Protocol.support_cutoff S.E d := by
      rw [← vote_time_add_delta]
      exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
    have hcutHor : Protocol.support_cutoff S.E d ≤ rho.horizon := by
      rw [← Protocol.a_eq_support_cutoff_succ S.hc S.E r]
      exact hhor
    have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
      hvoteCut.trans hcutHor
    have hheads : ∀ x ∈ rho.honest,
        Block.Preceq B.erase (voterHeadAt S rho x d) := by
      intro x hx
      exact SettledBootstrapPreparedV4.honestProposal_preceq_voterHeadAt_core
        S adm hcom hboot hawake hfinality hs hsourceHor hprop hB
          (by simpa only [d] using hsr) hvoteHor hx
    have hlastHor : Protocol.confirmation_time S.E
        (S.hc.opening_slot r) ≤ rho.horizon := by
      rw [opening_confirmation_time_eq_action]
      exact hhor
    exact SettledBootstrapPreparedV4.commonAncestor_preceq_actionHeadAt_core
      S adm hcom hboot hawake hfinality hlastHor (hs.le.trans hsr)
        (le_refl _) hhor hv hheads

#print axioms SettledBootstrapPreparedV4.phaseShiftSafety_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
