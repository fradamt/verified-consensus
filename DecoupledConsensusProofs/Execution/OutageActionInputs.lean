module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section

/-! Exact named action inputs and finite historical voter sets. The proofs
start from the actual event fold and emitted full row. They add no remote
open, support, joint-invariant or outage-preservation assumption. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageInputs
open Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem no_attest_proposal (p : Prop) [Decidable p]
    (body : Option (NamedBlock V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then
      match body with
      | none => []
      | some B => [NamedObject.block B]
    else []) := by
  split_ifs <;> cases body <;> simp

omit [DecidableEq V] [Fintype V] in
theorem no_attest_vote (p : Prop) [Decidable p]
    (vote : Option (GoldfishVote V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then vote.toList.map NamedObject.gfVote else []) := by
  split_ifs <;> cases vote <;> simp

theorem attestation_suffix_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V) (prior : List (NamedObject V))
    (hprefix : NamedObject.attest a ∉ prior)
    (h : NamedObject.attest a ∈ (if t = S.a (S.hc.round_of st.core.s) ∧
        (S.node v).awake (S.hc.round_of st.core.s) = true then
      let out := Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st record
      (out.1, out.2.1, prior ++ [NamedObject.attest out.2.2])
    else (st, record, prior)).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  split_ifs at h with hact
  · simp only [List.mem_append, List.mem_singleton, hprefix, false_or,
      NamedObject.attest.injEq] at h
    subst a
    exact ⟨hact.1, hact.2, S.node_val_index v⟩
  · exact False.elim (hprefix h)

/-- The scheduler's final guard and the original row agree on the action round. -/
theorem tick_attestation_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V)
    (h : NamedObject.attest a ∈
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  rw [NamedTick.tick_computed_duties] at h
  dsimp only at h
  apply attestation_suffix_fields gc S v _ record t a _ ?_ h
  simp only [List.mem_append, no_attest_vote, or_false]
  exact no_attest_proposal _ _ a

theorem action_slot_pos (S : Setup V) (r : Round) :
    0 < S.E.slotOf (S.a r) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
  exact Nat.zero_lt_succ _

theorem action_support_time (S : Setup V) (r : Round) :
    S.a r = Protocol.support_cutoff S.E (S.E.slotOf (S.a r)) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]

theorem action_read_round (S : Setup V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (actionReadFrom S before r).st.core.s = r :=
  Proofs.HealingLemmas.round_of_slotOf_a S r

/-- At a round action the proposal and vote branches are absent by their times.
The remaining duty receives the restricted statement's computed action read. -/
theorem tick_at_action (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    (Execution.NamedNode.tick S v before (S.a r)).2 =
      let n := actionReadFrom S before r
      let gc := NamedProfile.gradeContract n.cache
      if (S.node v).awake r = true then
        [NamedObject.attest
          (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st n.record).2.2]
      else [] := by
  have hpos := action_slot_pos S r
  have hs := action_support_time S r
  have hp : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.proposal_time S.E (S.E.slotOf (S.a r)) ∧
      S.E.proposer (S.E.slotOf (S.a r)) = (S.node v).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.vote_time S.E (S.E.slotOf (S.a r))) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E _ (hs.symm.trans h.2)
  change (Protocol.NamedTick.tick (NamedProfile.gradeContract (preparedCache S before (S.a r)))
    S.E S.hc S.cfg (S.node v) before.st before.record (S.a r)).2.2 = _
  rw [NamedTick.tick_computed_duties]
  simp only [if_neg hp, if_neg hv, if_pos (And.intro hpos hs), List.nil_append]
  have hround : S.hc.round_of (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract (preparedCache S before (S.a r))) S.E S.hc
      (Protocol.NamedStore.setClock S.E before.st (S.a r)) (S.E.slotOf (S.a r) - 1)).core.s = r :=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  simp only [hround, true_and]
  split_ifs <;> rfl

theorem action_read_invariant (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st := by
  apply Proofs.NamedConfirmationMembership.invariant_update
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1

theorem emitted_attestation_stages (S : Setup V) (rho : NamedRun V)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t ∧
      let before := NamedRun.stateBefore S rho i v
      let n := actionReadFrom S before a.round
      let gc := NamedProfile.gradeContract n.cache
      (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v)
        n.st n.record).2.2 = a ∧
      a.val_index = v ∧ a.round = S.hc.round_of n.st.core.s ∧
      t = S.a a.round ∧ (S.node v).awake a.round = true := by
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨ht, hawake, hval⟩ := tick_attestation_fields _ S v _ _ t a ho
  subst t
  have ha := ho
  change NamedObject.attest a ∈
    (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) (S.a a.round)).2 at ha
  rw [tick_at_action] at ha
  simp only [if_pos hawake, List.mem_singleton, NamedObject.attest.injEq] at ha
  exact ⟨i, hi, ho, ha.symm, hval, (action_read_round S _ a.round).symm, rfl, hawake⟩

theorem emitted_attestation_head (S : Setup V) (rho : NamedRun V)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t ∧
      let n := actionReadFrom S (NamedRun.stateBefore S rho i v) a.round
      ∃ H : NamedBlock V, H ∈ n.st.bodies ∧ a.confirmed = some H.root := by
  obtain ⟨i, hi, ho, hrow, _⟩ := emitted_attestation_stages S rho hem
  refine ⟨i, hi, ho, ?_⟩
  let n := actionReadFrom S (NamedRun.stateBefore S rho i v) a.round
  have hinv := action_read_invariant S rho i v a.round
  obtain ⟨B, hB, hhead⟩ := Proofs.NamedConfirmationMembership.attestation_input_head n.cache
    S.E S.hc S.cfg (S.node v) n.st hinv
  have htree : n.st.core.T = n.st.bodies.image NamedBlock.erase := hinv.1.1.1
  rw [htree] at hB
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hB
  refine ⟨H, hH, ?_⟩
  have hconfirmed := congrArg NamedAttestation.confirmed hrow
  change (Protocol.attestation_input_with (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st.core.toHealing).confirmed = a.confirmed at hconfirmed
  exact hconfirmed.symm.trans (hhead.trans (congrArg some (Proofs.NamedWire.erase_root H)))



theorem window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega



#print axioms action_read_invariant
#print axioms emitted_attestation_stages
#print axioms emitted_attestation_head
end DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageInputs

end
