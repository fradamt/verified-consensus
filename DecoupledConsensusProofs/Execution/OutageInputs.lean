module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Objects.AwakeWindowQuorum

@[expose] public section

/-! Exact named action inputs and finite historical voter sets. The proofs
start from the actual event fold and emitted full row. They add no remote
open, support, joint-invariant or outage-preservation assumption. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_proposal (p : Prop) [Decidable p]
    (body : Option (NamedBlock V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then
      match body with
      | none => []
      | some B => [NamedObject.block B]
    else []) := by
  split_ifs <;> cases body <;> simp

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_vote (p : Prop) [Decidable p]
    (vote : Option (GoldfishVote V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then vote.toList.map NamedObject.gfVote else []) := by
  split_ifs <;> cases vote <;> simp

private theorem attestation_suffix_fields (gc : Protocol.GradeContract V) (S : Setup V)
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
private theorem tick_attestation_fields (gc : Protocol.GradeContract V) (S : Setup V)
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



private theorem action_read_round (S : Setup V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (actionReadFrom S before r).st.core.s = r :=
  (NamedActionSources.action_timing S before r).2.2

/-- At a round action the proposal and vote branches are absent by their times.
The remaining duty receives the restricted statement's computed action read. -/
private theorem tick_at_action (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    (Execution.NamedNode.tick S v before (S.a r)).2 =
      let n := actionReadFrom S before r
      let gc := NamedProfile.gradeContract n.cache
      if (S.node v).awake r = true then
        [NamedObject.attest
          (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st n.record).2.2]
      else [] :=
  NamedActionSources.tick_at_action S v before r

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

theorem emittedInRound_iff (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) :
    emittedInRound S rho v k = true ↔
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        NamedRun.emits S rho v (.attest a) (S.a k) := by
  constructor
  · intro h
    obtain ⟨i, _, hs⟩ := List.any_eq_true.mp h
    cases he : rho.events[i]? with
    | none => simp [he] at hs
    | some e =>
      cases e with
      | deliver u o t => simp [he] at hs
      | tick u t =>
        by_cases hg : u = v ∧ t = S.a k
        · simp only [he, if_pos hg] at hs
          obtain ⟨o, ho, hrow⟩ := List.any_eq_true.mp hs
          cases o with
          | block B => cases hrow
          | gfVote b => cases hrow
          | attest a =>
            have hf : a.val_index = v ∧ a.round = k := of_decide_eq_true hrow
            refine ⟨a, hf.1, hf.2, ?_⟩
            obtain ⟨rfl, rfl⟩ := hg
            exact ⟨i, he, ho⟩
        · simp only [he, if_neg hg, Bool.false_eq_true] at hs
  · rintro ⟨a, hval, hr, i, hi, ho⟩
    apply List.any_eq_true.mpr
    refine ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
    simp only [hi]
    apply List.any_eq_true.mpr
    exact ⟨NamedObject.attest a, ho, decide_eq_true ⟨hval, hr⟩⟩

theorem honestRoundVoters_iff (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) :
    v ∈ honestRoundVoters S rho k ↔ v ∈ rho.honest ∧
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        NamedRun.emits S rho v (.attest a) (S.a k) := by
  simp only [honestRoundVoters, Finset.mem_filter, emittedInRound_iff]

private theorem window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega

theorem historical_of_vote (S : Setup V) (rho : NamedRun V)
    {u : V} {k r : Round} (hlo : r - S.hc.η_SG ≤ k) (hbefore : k + 1 < r)
    (hvote : u ∈ honestRoundVoters S rho k) :
    u ∈ historicalHonestVoters S rho r := by
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlo, hbefore⟩, hvote⟩
  exact Nat.lt_trans (Nat.lt_succ_self k) hbefore

theorem stale_of_eligible_vote (S : Setup V) (rho : NamedRun V)
    {u : V} {k r : Round} (hwindow : k ∈ Protocol.latest_window S.hc.η_SG r)
    (hvote : u ∈ honestRoundVoters S rho k)
    (hnot : u ∉ honestRoundVoters S rho (r - 1)) :
    u ∈ staleHistoricalVoters S rho r := by
  obtain ⟨hlo, hlt⟩ := window_bounds hwindow
  have hne : k ≠ r - 1 := by intro heq; exact hnot (heq ▸ hvote)
  have before : ∀ k r : Nat, k < r → k ≠ r - 1 → k + 1 < r := by
    intro k r h1 h2
    omega
  have hbefore := before k r hlt hne
  exact Finset.mem_sdiff.mpr ⟨historical_of_vote S rho hlo hbefore hvote, hnot⟩

section BoundaryQuorum
open Internal.NamedStableChainOutage

/-- The formation margin puts the round `s + 1` action inside the run.
Copied without change from the private helper in `NamedFinalityGuard`. -/
private theorem formation_round_covered (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0) :
    RoundCovered S rho (s + 1) := by
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_three; omega
  have hN : 0 < (s + 1) * S.hc.R := Nat.mul_pos (Nat.succ_pos s) hR
  have hN1 : 1 ≤ (s + 1) * S.hc.R := hN
  have hcast : (1 : Time) ≤ ((s + 1) * S.hc.R : Nat) := by exact_mod_cast hN1
  have hdelta := S.E.Δ_pos
  have hopen : 4 * S.E.Δ ≤
      4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) := by
    have hm := Int.mul_le_mul_of_nonneg_left hcast
      (show (0 : Int) ≤ 4 * S.E.Δ from
        Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
    simpa only [mul_one] using hm
  have hbudget :
      4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) + 2 * S.E.Δ + S.E.Δ ≤ b0 := by
    simpa only [formationConfirmationTime, Protocol.support_cutoff,
      Env.t, slotStart, Protocol.HealConfig.opening_slot] using
      old_margin_of_new S s b0 hmargin
  have hhor : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  apply Or.inr
  refine ⟨DecoupledConsensusModel.Protocol.Phase.g2, ?_, ?_⟩
  · change 0 ≤ 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) + (-1) * S.E.Δ
    have hA : S.E.Δ ≤
        4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) := by
      have hdelta4 : S.E.Δ ≤ 4 * S.E.Δ := by
        calc
          S.E.Δ = 1 * S.E.Δ := by ring
          _ ≤ 4 * S.E.Δ :=
            Int.mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt S.E.Δ_pos)
      exact hdelta4.trans hopen
    rw [neg_mul, one_mul]
    exact sub_nonneg.mpr hA
  · change 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) + (-1) * S.E.Δ ≤ rho.horizon
    have hstep :
        4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) + (-1) * S.E.Δ ≤
          4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Time) + 2 * S.E.Δ + S.E.Δ := by
      have hsmall : (-1) * S.E.Δ ≤ 2 * S.E.Δ + S.E.Δ := by
        calc
          (-1) * S.E.Δ ≤ 3 * S.E.Δ :=
            Int.mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt S.E.Δ_pos)
          _ = 2 * S.E.Δ + S.E.Δ := by ring
      rw [add_assoc]
      exact add_le_add_right hsmall _
    exact hstep.trans (hbudget.trans hhor)

/-- Public export of the faulty-weight bound at the outage boundary. The
sleepy condition at the covered round `s + 1` gives an awake-window majority,
so the non-honest weight stays below one quorum. The same statement is proved
privately inside `NamedConflictingCarrierBand`, `NamedFGProtection` and
`NamedFinalityGuard`; this copy is the one downstream modules may use. -/
theorem boundary_faulty_lt_quorum (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) :
    S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q := by
  exact AwakeWindowQuorum.faulty_weight_lt_quorum S.E
    (fun v => (S.node v).awake) rho.honest S.hc.η_SG (s + 1)
    (hsleep (s + 1) (Nat.succ_pos s)
      (formation_round_covered S rho b0 b1 s hexec hmargin))

#print axioms boundary_faulty_lt_quorum

end BoundaryQuorum

#print axioms action_read_invariant
#print axioms emitted_attestation_stages
#print axioms emitted_attestation_head
end DecoupledConsensusModel.Proofs.NamedOutageInputs

end
