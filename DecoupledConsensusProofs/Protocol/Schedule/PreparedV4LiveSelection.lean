module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Execution.PreparedV4ProtectedVoteAtVoteCore

@[expose] public section

/-! # Prepared V4 live-confirmed selections -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem confirmationTime_lt_nextVote_of_lt_v4
    (E : Env V) {q d : Slot} (hqd : q < d) :
    Protocol.confirmation_time E q < Protocol.vote_time E (d + 1) := by
  have hnext : Protocol.vote_time E (d + 1) =
      Protocol.vote_time E d + 4 * E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    push_cast
    ring
  rw [← vote_time_succ_add_delta_eq_confirmation_time E q, hnext]
  have hle := vote_time_mono_slots E (Nat.succ_le_of_lt hqd)
  have harith : ∀ a b z : Int, a ≤ b → 0 < z → a + z < b + 4 * z := by
    intro a b z hab hz
    omega
  exact harith _ _ _ hle E.Δ_pos

private theorem confirmationTime_mono_v4
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right h 1)

private theorem liveField_preceq_at_prefix_of_suffixSelections_v4
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

/-- The prepared V4 continuation protects genuine and fallback live selections. -/
theorem SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last q d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_protectedVoteSlots_core :
      ∀ {last : Slot}, Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ d, start ≤ d → d ≤ last + 1 →
        ProtectedVoteSlot S rho d P.erase ∧
        (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
          ∀ w ∈ rho.honest, ∀ B,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
            S.E S.hc (confStore S rho w q) q B →
            ProtectedVoteSlot S rho d B))
    (_of_actionSources_preceq_voteDutyHead_core :
      ∀ {last d : Slot}, Protocol.confirmation_time S.E last ≤ rho.horizon →
      start ≤ d → d ≤ last + 1 →
      ∀ {x : V}, x ∈ rho.honest →
      ∀ r, base + S.hc.η_SG ≤ r →
        S.a r < Protocol.vote_time S.E (d + 1) →
        (∀ w ∈ rho.honest,
          NamedRun.emits S rho w
            (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) (voterHeadAt S rho x d)) ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG)
            (voterHeadAt S rho x d) ∧
          ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
            Block.Preceq T (voterHeadAt S rho x d)))
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    (hq : S.hc.opening_slot (base + S.hc.η_SG) ≤ q) (hqd : q < d)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q).live_confirmed
      (voterHeadAt S rho x d) := by
  have hslot := _of_protectedVoteSlots_core hhor d hd hupper
  let contract := NamedProfile.gradeContract
    (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache
  by_cases hg : confEligible S.E (confStore S rho w q) q
      (confWalkWith contract S.E S.hc (confStore S rho w q) q) = true
  · exact (hslot.2 q hq hqd w hw _ ⟨rfl, hg⟩).heads x hx
  · rw [update_confirmation_with_live_confirmed, if_neg hg]
    have hcutpos : 0 < base + S.hc.η_SG :=
      Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt S.hc.η_SG_ge_one)
        (Nat.le_add_left _ _)
    have hmajority := honestWeightMajority_of_finiteWindowsFrom S hawake hcutpos
      (hboot.settled.trans hd) hupper hhor
    have hread : S.a (base + S.hc.η_SG) ≤
        Protocol.confirmation_time S.E q := by
      change Protocol.confirmation_time S.E
        (S.hc.opening_slot (base + S.hc.η_SG)) ≤ _
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.add_le_add_right hq 1)
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.confirmation_time S.E q)).toHealing.toFG)
        (voterHeadAt S rho x d) := by
      rcases WeakFG.fgRoot_confirmationWitness_at_read S adm hmajority hw
          (Protocol.confirmation_time S.E q) with
        hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
      · rw [hgen]
        exact Protocol.preceq_genesis _
      · by_cases hold : a.round < base + S.hc.η_SG
        · exact Block.preceq_trans
            (WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read S adm
              hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
              ((min_le_left _ _).trans hread) hC hJ ha hemit hold hpair hT)
            (hslot.1.heads x hx)
        · have hat : S.a a.round < Protocol.vote_time S.E (d + 1) := by
            have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
            rw [← htime]
            exact ht.trans (confirmationTime_lt_nextVote_of_lt_v4 S.E hqd)
          exact ((_of_actionSources_preceq_voteDutyHead_core hhor hd hupper hx
            a.round (Nat.le_of_not_gt hold) hat).2 a.val_index ha).2 _ hT
    simpa only [contract, confRoot, confStore, tickStore] using hroot

#print axioms SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core_of_pins

/-- Pin-free read-horizon selection bound from the available V4 protected-slot
and action-source folds. -/
theorem SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last q d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    (hq : S.hc.opening_slot (base + S.hc.η_SG) ≤ q) (hqd : q < d)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q).live_confirmed
      (voterHeadAt S rho x d) := by
  exact SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun hhor' => SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor')
      (fun {last} {d} hhor' hd' hupper' {x} hx' =>
        SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux
          S adm hcom hboot hawake hfinality hhor' hd' hupper' hx')
      hhor hd hupper hq hqd hw hx

#print axioms SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core

/-- The reported live field at a covered read is below each protected destination head. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_protectedVoteSlots_core :
      ∀ {last : Slot}, Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ d, start ≤ d → d ≤ last + 1 →
        ProtectedVoteSlot S rho d P.erase ∧
        (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
          ∀ w ∈ rho.honest, ∀ B,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
            S.E S.hc (confStore S rho w q) q B →
            ProtectedVoteSlot S rho d B))
    (_of_actionSources_preceq_voteDutyHead_core :
      ∀ {last d : Slot}, Protocol.confirmation_time S.E last ≤ rho.horizon →
      start ≤ d → d ≤ last + 1 →
      ∀ {x : V}, x ∈ rho.honest →
      ∀ r, base + S.hc.η_SG ≤ r →
        S.a r < Protocol.vote_time S.E (d + 1) →
        (∀ w ∈ rho.honest,
          NamedRun.emits S rho w
            (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) (voterHeadAt S rho x d)) ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG)
            (voterHeadAt S rho x d) ∧
          ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
            Block.Preceq T (voterHeadAt S rho x d)))
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1) {t : Time}
    (hlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t)
    (hhi : t < Protocol.confirmation_time S.E d)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (voterHeadAt S rho x d) := by
  let cut := S.hc.opening_slot (base + S.hc.η_SG)
  have hcutd : cut < d := by
    by_contra h
    exact (not_lt_of_ge
      (confirmationTime_mono_v4 S.E (Nat.le_of_not_gt h))) (hlo.trans_lt hhi)
  have hcutHor : Protocol.confirmation_time S.E cut ≤ rho.horizon :=
    (confirmationTime_mono_v4 S.E
      (Nat.le_of_lt_succ (hcutd.trans_le hupper))).trans hhor
  let m := (rho.events.filter (fun e =>
    decide (e.time ≤ Protocol.confirmation_time S.E cut))).length
  have hbase : Block.Preceq (rho.stateBefore S m v).st.live_confirmed
      (voterHeadAt S rho x d) := by
    have hsel :=
      SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core_of_pins
        S adm hcom hboot hawake hfinality _of_protectedVoteSlots_core
          _of_actionSources_preceq_voteDutyHead_core hhor hd hupper
          (le_refl cut) hcutd hv hx
    have hsel' : Block.Preceq
        (rho.storeAt S v
          (Protocol.confirmation_time S.E cut)).live_confirmed
        (voterHeadAt S rho x d) := by
      rw [live_confirmed_eq_update
        S adm.toNamedScheduleWellFormed hv cut hcutHor]
      simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hsel
    simpa only [Run.storeAt,
      stateAt_eq_take S adm.toNamedScheduleWellFormed, m] using hsel'
  rw [Run.storeAt, stateAt_eq_take S adm.toNamedScheduleWellFormed]
  apply liveField_preceq_at_prefix_of_suffixSelections_v4
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
  have hqAfter : Protocol.confirmation_time S.E cut <
      Protocol.confirmation_time S.E q := by
    have h := filter_false_of_index_ge S adm.toNamedScheduleWellFormed _
      (downward_le (Protocol.confirmation_time S.E cut)) hmi hqevent
    simpa only [decide_eq_false_iff_not, not_le, Event.time] using h
  have hqlo : cut ≤ q := by
    by_contra h
    exact (not_lt_of_ge (confirmationTime_mono_v4 S.E
      (Nat.le_of_lt (Nat.lt_of_not_ge h)))) hqAfter
  have hqhi : q < d := by
    by_contra h
    exact (not_lt_of_ge
      (confirmationTime_mono_v4 S.E (Nat.le_of_not_gt h))) hqBefore
  rw [← hCprepared]
  exact SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core_of_pins
    S adm hcom hboot hawake hfinality _of_protectedVoteSlots_core
      _of_actionSources_preceq_voteDutyHead_core hhor hd hupper
      hqlo hqhi hv hx

#print axioms SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core_of_pins

/-- Pin-free covered-read live bound from the available V4 folds. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1) {t : Time}
    (hlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t)
    (hhi : t < Protocol.confirmation_time S.E d)
    {v x : V} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (voterHeadAt S rho x d) := by
  exact SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun hhor' => SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor')
      (fun {last} {d} hhor' hd' hupper' {x} hx' =>
        SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux
          S adm hcom hboot hawake hfinality hhor' hd' hupper' hx')
      hhor hd hupper hlo hhi hv hx

#print axioms SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
