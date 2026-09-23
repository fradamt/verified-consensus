module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Execution.PreparedV4ActionSourcesCore
public import DecoupledConsensusProofs.Objects.PreparedV4ProtectedVoteSlotsCore
public import DecoupledConsensusProofs.Objects.WeakLegacySources
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-! # Finalized-read head bound after the prepared V4 handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_storeAt_eq_storeBeforeTime_succ
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    rho.storeAt S v t = rho.storeBeforeTime S v (t + 1) := by
  have hbool (a b : Int) : decide (a ≤ b) = decide (a < b + 1) := by
    simp only [Int.lt_add_one_iff]
  have hfilter : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.filter (fun e => decide (e.time < t + 1)) :=
    List.filter_congr (fun e _ => hbool e.time t)
  have hstate : NamedRun.readAt S rho t =
      NamedRun.stateBeforeTime S rho (t + 1) := by
    unfold NamedRun.readAt NamedRun.stateBeforeTime
    rw [hfilter]
  unfold Run.storeAt Run.storeBeforeTime
  rw [hstate]

private theorem preparedV4_finalized_preceq_fgRoot_at_read
    (S : Setup V) {rho : Run V} (v : V) (t : Time) :
    Block.Preceq (rho.storeBeforeTime S v t).core.F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).core.toHealing.toFG) := by
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho t v
  exact Proofs.Records.preceq_get_fg_root_of_F
    (st := (rho.storeBeforeTime S v t).core.toHealing.toFG) hFJ

private theorem preparedV4_confirmationHorizon_max
    (S : Setup V) {rho : Run V} {s t : Slot}
    (hs : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (ht : Protocol.confirmation_time S.E t ≤ rho.horizon) :
    Protocol.confirmation_time S.E (max s t) ≤ rho.horizon := by
  rcases le_total s t with h | h
  · simpa only [max_eq_right h] using ht
  · simpa only [max_eq_left h] using hs

private theorem preparedV4_confirmationTime_lt_nextVote
    (E : Env V) {q d : Slot} (hqd : q < d) :
    Protocol.confirmation_time E q < Protocol.vote_time E (d + 1) := by
  have hnext : Protocol.vote_time E (d + 1) =
      Protocol.vote_time E d + 4 * E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    push_cast
    ring
  rw [← vote_time_succ_add_delta_eq_confirmation_time E q, hnext]
  have hle := vote_time_mono_slots E (Nat.succ_le_of_lt hqd)
  have harith : ∀ a b z : Int, a ≤ b → 0 < z →
      a + z < b + 4 * z := by
    intro a b z hab hz
    omega
  exact harith _ _ _ hle E.Δ_pos

/-- A finalized read after the V4 handover has an actual source slot whose
successor heads extend it. This is the source-event route: previous sources use the
finite V4 bootstrap, and recent sources use their emitted action witness. -/
theorem SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (protectedVoteSlots_core_of_pins :
      ∀ {last : Slot},
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ d, start ≤ d → d ≤ last + 1 →
        ProtectedVoteSlot S rho d P.erase ∧
        (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
          ∀ w ∈ rho.honest, ∀ B,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
            S.E S.hc (confStore S rho w q) q B →
            ProtectedVoteSlot S rho d B))
    (actionSources_preceq_voteDutyHead_core_of_pins :
      ∀ {last d : Slot},
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      start ≤ d → d ≤ last + 1 →
      ∀ {x : V}, x ∈ rho.honest →
      ∀ r, base + S.hc.η_SG ≤ r →
        S.a r < Protocol.vote_time S.E (d + 1) →
        (∀ w ∈ rho.honest,
          NamedRun.emits S rho w
            (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r)
            (voterHeadAt S rho x d)) ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG)
            (voterHeadAt S rho x d) ∧
          ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
            Block.Preceq T (voterHeadAt S rho x d)))
    {w : V} (hw : w ∈ rho.honest) {u : Time}
    (hu : Protocol.confirmation_time S.E start ≤ u) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S w u).core.F
            (voterHeadAt S rho x (last + 1)) := by
  have hcutPos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hmajority : HonestWeightMajority S rho.honest :=
    honestWeightMajority_of_finiteWindowsFrom S hawake hcutPos hboot.settled
      (Nat.le_succ start) hstartHor
  have hF := preparedV4_finalized_preceq_fgRoot_at_read
    S (rho := rho) w (u + 1)
  rw [preparedV4_storeAt_eq_storeBeforeTime_succ S rho w u]
  rcases WeakFG.fgRoot_confirmationWitness_at_read
      S adm hmajority hw (u + 1) with
    hgen | ⟨C, hC, hJ, a, ta, ha, hemit, _, hpair, hT⟩
  · refine ⟨start, le_rfl, hstartHor, ?_⟩
    intro last _ _ x _
    rw [hgen] at hF
    exact Block.preceq_trans hF (Protocol.preceq_genesis _)
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have haHor : S.a a.round ≤ rho.horizon := by
      obtain ⟨i, hi, _⟩ := hemit
      have h := (adm.toNamedScheduleWellFormed.in_horizon _
        (List.mem_of_getElem? hi)).2
      simpa only [Event.time, htime] using h
    by_cases hold : a.round < base + S.hc.η_SG
    · have hboundary : min (S.a (base + S.hc.η_SG))
          (Protocol.vote_time S.E start) ≤ u + 1 :=
        (min_le_right _ _).trans
          ((vote_time_le_confirmation_time S.E start).trans
            (hu.trans (Int.le_add_of_nonneg_right (by decide))))
      have hrootP := WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read
        S adm hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
        hboundary hC hJ ha hemit hold hpair hT
      refine ⟨start, le_rfl, hstartHor, ?_⟩
      intro last hlast hlastHor x hx
      have hP := (protectedVoteSlots_core_of_pins hlastHor
        (last + 1) (hlast.trans (Nat.le_succ _)) (le_refl _)).1.heads x hx
      exact Block.preceq_trans hF (Block.preceq_trans hrootP hP)
    · let source := S.hc.opening_slot a.round
      let first := max start source
      have hsourceHor : Protocol.confirmation_time S.E source ≤ rho.horizon := by
        simpa only [source, opening_confirmation_time_eq_action] using haHor
      have hfirstHor : Protocol.confirmation_time S.E first ≤ rho.horizon :=
        preparedV4_confirmationHorizon_max S hstartHor hsourceHor
      refine ⟨first, Nat.le_max_left _ _, hfirstHor, ?_⟩
      intro last hlast hlastHor x hx
      have hsourceLast : source ≤ last := (Nat.le_max_right _ _).trans hlast
      have hat : S.a a.round < Protocol.vote_time S.E ((last + 1) + 1) := by
        rw [← opening_confirmation_time_eq_action S a.round]
        exact preparedV4_confirmationTime_lt_nextVote S.E
          (Nat.lt_succ_of_le hsourceLast)
      have haction := actionSources_preceq_voteDutyHead_core_of_pins
        hlastHor (Nat.le_max_left start source |>.trans hlast |>.trans
          (Nat.le_succ _)) (le_refl _) hx a.round (Nat.le_of_not_gt hold) hat
      exact Block.preceq_trans hF ((haction.2 a.val_index ha).2 _ hT)

#print axioms SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_pins


/-- Item 1 is available; only the post-cut action-source producer remains pinned. -/
theorem SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_action_pin
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (actionSources_preceq_voteDutyHead_core_of_pins :
      ∀ {last d : Slot},
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      start ≤ d → d ≤ last + 1 →
      ∀ {x : V}, x ∈ rho.honest →
      ∀ r, base + S.hc.η_SG ≤ r →
        S.a r < Protocol.vote_time S.E (d + 1) →
        (∀ w ∈ rho.honest,
          NamedRun.emits S rho w
            (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r)
            (voterHeadAt S rho x d)) ∧
        (∀ w ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG)
            (voterHeadAt S rho x d) ∧
          ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
            Block.Preceq T (voterHeadAt S rho x d)))
    {w : V} (hw : w ∈ rho.honest) {u : Time}
    (hu : Protocol.confirmation_time S.E start ≤ u) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S w u).core.F
            (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_pins
    S adm hcom hboot hawake hfinality hstartHor
      (fun hhor => SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor)
      actionSources_preceq_voteDutyHead_core_of_pins hw hu

#print axioms SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_action_pin

/-- Closed continuation-side finalized-read bound. -/
theorem SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {u : Time}
    (hu : Protocol.confirmation_time S.E start ≤ u) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S w u).core.F
            (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core_of_action_pin
    S adm hcom hboot hawake hfinality hstartHor
      (fun {last d} hhor hd hupper {x} hx =>
        SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality
            (last := last) (d := d) hhor hd hupper (x := x) hx)
      hw hu

#print axioms SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
