module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Execution.PreparedV4ActionSourcesCore
public import DecoupledConsensusProofs.Objects.PreparedV4ProtectedVoteSlotsCore
public import DecoupledConsensusProofs.Objects.WeakLegacySources

@[expose] public section

/-! # Prepared V4 FG-root common-head bound -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_confirmationHorizon_max_root
    (S : Setup V) {rho : Run V} {s t : Slot}
    (hs : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (ht : Protocol.confirmation_time S.E t ≤ rho.horizon) :
    Protocol.confirmation_time S.E (max s t) ≤ rho.horizon := by
  rcases le_total s t with h | h
  · simpa only [max_eq_right h] using ht
  · simpa only [max_eq_left h] using hs

private theorem preparedV4_confirmationTime_lt_nextVote_root
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

/-- Every read FG root has a common-head witness chosen from its actual action
source. -/
theorem SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start first : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
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
    (hfirst : Protocol.confirmation_time S.E first ≤ rho.horizon)
    (hstart : start ≤ first + 1) {t : Time}
    (hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    ∃ last : Slot, first ≤ last ∧
      Protocol.confirmation_time S.E last ≤ rho.horizon ∧
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w t).core.toHealing.toFG)
        (voterHeadAt S rho x (last + 1)) := by
  have hcutPos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hmajority : HonestWeightMajority S rho.honest :=
    honestWeightMajority_of_finiteWindowsFrom
      S hawake hcutPos hboot.settled hstart hfirst
  rcases WeakFG.fgRoot_confirmationWitness_at_read
      S adm hmajority hw t with
    hgen | ⟨C, hC, hJ, a, ta, ha, hemit, _, hpair, hT⟩
  · exact ⟨first, le_rfl, hfirst, by
      rw [hgen]
      exact Protocol.preceq_genesis _⟩
  · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have haHor : S.a a.round ≤ rho.horizon := by
      obtain ⟨i, hi, _⟩ := hemit
      have h := (adm.toNamedScheduleWellFormed.in_horizon _
        (List.mem_of_getElem? hi)).2
      simpa only [Event.time, htime] using h
    let source := S.hc.opening_slot a.round
    let last := max first source
    have hfirstLast : first ≤ last := Nat.le_max_left _ _
    have hsourceLast : source ≤ last := Nat.le_max_right _ _
    have hsourceHor : Protocol.confirmation_time S.E source ≤ rho.horizon := by
      simpa only [source, opening_confirmation_time_eq_action] using haHor
    have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon :=
      preparedV4_confirmationHorizon_max_root S hfirst hsourceHor
    have hd : start ≤ last + 1 :=
      hstart.trans (Nat.add_le_add_right hfirstLast 1)
    refine ⟨last, hfirstLast, hlastHor, ?_⟩
    by_cases hold : a.round < base + S.hc.η_SG
    · have hrootP := WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read
        S adm hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
        hread hC hJ ha hemit hold hpair hT
      exact Block.preceq_trans hrootP
        ((protectedVoteSlots_core_of_pins hlastHor
          (last + 1) hd (le_refl _)).1.heads x hx)
    · have hat : S.a a.round < Protocol.vote_time S.E ((last + 1) + 1) := by
        rw [← opening_confirmation_time_eq_action S a.round]
        exact preparedV4_confirmationTime_lt_nextVote_root S.E
          (Nat.lt_succ_of_le hsourceLast)
      exact ((actionSources_preceq_voteDutyHead_core_of_pins
        hlastHor hd (le_refl _) hx a.round (Nat.le_of_not_gt hold) hat).2
          a.val_index ha).2 _ hT

#print axioms SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_pins


/-- Item 1 is available; only the post-cut action-source producer remains pinned. -/
theorem SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_action_pin
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start first : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
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
    (hfirst : Protocol.confirmation_time S.E first ≤ rho.horizon)
    (hstart : start ≤ first + 1) {t : Time}
    (hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    ∃ last : Slot, first ≤ last ∧
      Protocol.confirmation_time S.E last ≤ rho.horizon ∧
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w t).core.toHealing.toFG)
        (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun hhor => SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor)
      actionSources_preceq_voteDutyHead_core_of_pins
      hfirst hstart hread hw hx

#print axioms SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_action_pin

/-- Closed continuation-side FG-root common-head bound. -/
theorem SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start first : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hfirst : Protocol.confirmation_time S.E first ≤ rho.horizon)
    (hstart : start ≤ first + 1) {t : Time}
    (hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    ∃ last : Slot, first ≤ last ∧
      Protocol.confirmation_time S.E last ≤ rho.horizon ∧
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w t).core.toHealing.toFG)
        (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core_of_action_pin
    S adm hcom hboot hawake hfinality
      (fun {last d} hhor hd hupper {x} hx =>
        SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality
            (last := last) (d := d) hhor hd hupper (x := x) hx)
      hfirst hstart hread hw hx

#print axioms SettledBootstrapPreparedV4.fgRoot_at_read_has_vote_head_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
