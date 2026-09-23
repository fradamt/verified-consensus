module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.StableRootSuffixOrigin
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section

/-!
# T_out, step 1: inclusive stable-record provenance

The public `storeAt` read includes events at the cutoff. This leaf converts
that read to the indexed event fold and then adds the time and round bounds
needed by the outage canonicity route.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem stableRoot_origin_time_le
    (S : Setup V) (rho : Run V) (v : V) (s : Round)
    {n i : Nat} (hi : i < n)
    (hprefix : ∀ j e, j < n → rho.events[j]? = some e → e.time ≤ S.a s)
    {G : Block V} (hroot : StableRecord.StableRootAt S rho v i G) :
    ∃ time : Time,
      rho.events[i]? = some (.tick v time) ∧
        time ≤ S.a s ∧
        0 < S.E.slotOf time ∧
        time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
        DecoupledConsensusModel.Protocol.frameStableRoot
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).cache S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).st.core.toHealing
          (S.hc.round_of
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S i v) time).st.core.s) = some G := by
  rcases hroot with ⟨time, hiTime, hpos, hcut, hframe⟩
  exact ⟨time, hiTime, hprefix i _ hi hiTime, hpos, hcut, hframe⟩

theorem stableRoot_origin_round_le
    (S : Setup V) (s : Round) {time : Time}
    (hTime : time ≤ S.a s) (hpos : 0 < S.E.slotOf time)
    (hcut : time = Protocol.support_cutoff S.E (S.E.slotOf time)) :
    S.hc.round_of (S.E.slotOf time) ≤ s := by
  have hcutLe : Protocol.support_cutoff S.E (S.E.slotOf time) ≤
      Protocol.support_cutoff S.E (S.hc.opening_slot s + 1) := by
    have hTime' : time ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot s) := by
      simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hTime
    calc
      Protocol.support_cutoff S.E (S.E.slotOf time) = time := hcut.symm
      _ ≤ Protocol.confirmation_time S.E (S.hc.opening_slot s) := hTime'
      _ = Protocol.support_cutoff S.E (S.hc.opening_slot s + 1) := by
        rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  have hslot : S.E.slotOf time ≤ S.hc.opening_slot s + 1 :=
    Proofs.Optimistic.slot_le_of_support_cutoff_le S.E hcutLe
  have hround : S.E.slotOf time / S.hc.R ≤
      (S.hc.opening_slot s + 1) / S.hc.R :=
    Nat.div_le_div_right hslot
  have hopen : S.hc.round_of (S.hc.opening_slot s + 1) = s :=
    Proofs.HealingLemmas.round_of_opening_succ S.hc s
  calc
    S.hc.round_of (S.E.slotOf time) ≤
        S.hc.round_of (S.hc.opening_slot s + 1) := hround
    _ = s := hopen

set_option maxHeartbeats 500000 in
/-- Every stable record observed by the inclusive round-`s` read is genesis or
was produced by an earlier confirmation tick. A non-genesis origin occurred
at a support cutoff whose frame round is at most `s`. -/
theorem stableOutput_inclusive_record_origin
    (S : Setup V) (rho : Run V) (b0 b1 : Time) (v : V) (s : Round)
    (hout : OutageExecution S rho b0 b1) :
    ∃ n : Nat,
      rho.storeAt S v (S.a s) = (rho.stateBefore S n v).st ∧
      ((rho.stateBefore S n v).st.latest_stable = Block.genesis ∨
        ∃ i : Nat, ∃ r : Round, i < n ∧ r ≤ s ∧
          ∃ time : Time,
            rho.events[i]? = some (.tick v time) ∧
              time ≤ S.a s ∧
              0 < S.E.slotOf time ∧
              time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
              r = S.hc.round_of (S.E.slotOf time) ∧
              StableRecord.StableRootAt S rho v i
                (rho.stateBefore S n v).st.latest_stable) := by
  have sch : ScheduleWellFormed S rho := hout.execution.toScheduleWellFormed
  obtain ⟨n, hn, hprefix⟩ := Proofs.NamedRuntime.readAt_eq_prefix S rho sch.sorted (S.a s)
  have hstore : rho.storeAt S v (S.a s) =
      (rho.stateBefore S n v).st := by
    unfold Run.storeAt
    rw [congrFun hn v]
  refine ⟨n, hstore, ?_⟩
  rcases StableRecord.stateBefore_latest_stable_rootOrigin S rho v n with hgen | ⟨i, hi, hroot⟩
  · exact Or.inl hgen
  · obtain ⟨time, hiTime, hTime, hpos, hcut, hframe⟩ :=
      stableRoot_origin_time_le S rho v s hi hprefix hroot
    have hr : S.hc.round_of (S.E.slotOf time) ≤ s :=
      stableRoot_origin_round_le S s hTime hpos hcut
    refine Or.inr ⟨i, S.hc.round_of (S.E.slotOf time), hi, hr, time, hiTime,
      hTime, hpos, hcut, rfl, ?_⟩
    exact hroot

#print axioms stableOutput_inclusive_record_origin

/-- General-time form: every stable record observed by the inclusive read at
`T` is genesis or was produced by an earlier confirmation tick at a support
cutoff at or before `T`. -/
theorem stableOutput_inclusive_record_origin_at
    (S : Setup V) (rho : Run V) (v : V) (T : Time)
    (hsorted : rho.events.Pairwise (fun e f : NamedEvent V => e.key ≤ f.key)) :
    ∃ n : Nat,
      rho.storeAt S v T = (rho.stateBefore S n v).st ∧
      ((rho.stateBefore S n v).st.latest_stable = Block.genesis ∨
        ∃ i : Nat, i < n ∧
          ∃ time : Time,
            rho.events[i]? = some (.tick v time) ∧
              time ≤ T ∧
              0 < S.E.slotOf time ∧
              time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
              StableRecord.StableRootAt S rho v i
                (rho.stateBefore S n v).st.latest_stable) := by
  obtain ⟨n, hn, hprefix⟩ := Proofs.NamedRuntime.readAt_eq_prefix S rho hsorted T
  have hstore : rho.storeAt S v T = (rho.stateBefore S n v).st := by
    unfold Run.storeAt
    rw [congrFun hn v]
  refine ⟨n, hstore, ?_⟩
  rcases StableRecord.stateBefore_latest_stable_rootOrigin S rho v n with hgen | ⟨i, hi, hroot⟩
  · exact Or.inl hgen
  · rcases hroot with ⟨time, hiTime, hpos, hcut, hframe⟩
    exact Or.inr ⟨i, hi, time, hiTime, hprefix i _ hi hiTime, hpos, hcut,
      ⟨time, hiTime, hpos, hcut, hframe⟩⟩

#print axioms stableOutput_inclusive_record_origin_at

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
