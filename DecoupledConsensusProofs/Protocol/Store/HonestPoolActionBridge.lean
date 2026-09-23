module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Concentration

@[expose] public section

/-!
# Honest SG-pool votes are exact Section 7 actions

An SG vote in a protocol pool is not only attributed data. Pool provenance
finds the processed combined attestation, authenticity traces an honest author
to its own emission, and the pool-round invariant identifies its action round.
The scheduled Section 7 action at that round is another emission by the same
validator. Honest one-per-round emission uniqueness therefore identifies the
two attestations and their SG projections.

This bridge needs no post-GST or relay premise. Receipt in the pool already
supplies a causal in-run emission, and that emission itself proves that the
corresponding action time lies in the run horizon.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The confirmation update inside `actionStoreAt` preserves the projected SG
pool. -/
theorem actionStoreAt_projectedSGVotes
    (S : Setup V) (rho : Run V) (w : V) (r : Round) :
    (actionStoreAt S rho w r).toHealing.sg_votes =
      (rho.storeBeforeTime S w (S.a r)).toHealing.sg_votes := rfl

/-- An SG vote in a round bucket, when attributed to an honest validator, is
that validator's exact Section 7 SG action vote for the bucket round.

The reader need not be honest. The only semantic premise is honesty of the
vote author. Pool provenance and authenticity supply the actual honest
emission and its in-horizon action time. -/
theorem honestSGVote_actionEmission_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest)
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k ∧
      rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) := by
  change u ∈
      ((rho.stateBeforeTime S time w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed time
  have haN : a ∈ (rho.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact ha
  have haround : a.round = k :=
    Proofs.NamedStoreBridge.sgRounds_stateBefore S rho n w k a
      (List.mem_toFinset.mp haN)
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have havu : a.val_index = u.val_index := by
      simpa only [Protocol.sgVote] using h
    exact havu.trans huv
  obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
    Proofs.Optimistic.processes_attest_of_mem_sg_pool S rho w n k a haN
  -- The pool row `a` was carried in by an actual attest emission or by a
  -- carried row on a processed block (Proofs.Optimistic.CarriesRow); either way its
  -- named source `row` is authentic.
  obtain ⟨row, hrowEq, t', hte, hemit⟩ :
      ∃ row : NamedAttestation V, a = row.erase ∧
        ∃ t' : Time, t' ≤ e.time ∧ rho.emits S row.val_index (Object.attest row) t' := by
    cases o with
    | block Bl =>
        obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
        have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
        have hrowHon : row.val_index ∈ rho.honest := by rw [hrowV]; exact hv
        obtain ⟨t', hte, hemit⟩ :=
          adm.carried_attest w Bl e.time hproc row hrowMem hrowHon
        exact ⟨row, hrowEq, t', hte, hemit⟩
    | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
    | attest row =>
        have hrowEq : a = row.erase := hcarry
        have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
        have hrowHon : row.val_index ∈ rho.honest := by rw [hrowV]; exact hv
        obtain ⟨t', hte, hemit⟩ :=
          adm.unforgeable w (Object.attest row) e.time hproc row.val_index hrowHon rfl
        exact ⟨row, hrowEq, t', hte, hemit⟩
  have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
  have hrowRound : row.round = k := by rw [hrowEq] at haround; exact haround
  have hemitV : rho.emits S v (Object.attest row) t' := hrowV ▸ hemit
  have hshape := Proofs.Optimistic.emits_attest_shape S hemitV
  have htime : t' = S.a k := by rw [hshape.2, hrowRound]
  have hemitVCopy := hemitV
  obtain ⟨i, hi, -⟩ := hemitVCopy
  have hiMem : Event.tick v t' ∈ rho.events := List.mem_of_getElem? hi
  have hactionHor : S.a k ≤ rho.horizon := by
    have h := (adm.in_horizon (Event.tick v t') hiMem).2
    simpa only [Event.time, htime] using h
  have hrowAction : row = actionAttestationAt S rho v k := by
    have hcanonical := ((NamedActionSources.action_run_emission S rho
      adm.toNamedScheduleWellFormed v k row).mp
      (by simpa only [htime] using hemitV)).2.2
    simpa only [hrowRound] using hcanonical
  refine ⟨?_, ?_⟩
  · calc
      u = Protocol.sgVote a := hau.symm
      _ = Protocol.sgVote row.erase := by rw [hrowEq]
      _ = Protocol.sgVote (actionAttestationAt S rho v k).erase := by rw [hrowAction]
      _ = actionSGVoteAt S rho v k := sgVote_actionAttestationAt S rho v k
  · rw [← hrowAction, ← htime]
    exact hemitV

/-- Exact SG projection at an arbitrary strict read. -/
theorem honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest)
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k :=
  (honestSGVote_actionEmission_of_mem_storeBeforeTime S adm hv hu huv).1


/-- The action-store form follows from the arbitrary strict-read bridge.
The confirmation update does not change the projected SG pool. -/
theorem honestSGVote_eq_actionSGVoteAt_of_mem_actionStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w v : V} {r k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest)
    (hu : u ∈ (actionStoreAt S rho w r).toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k := by
  rw [actionStoreAt_projectedSGVotes S rho w r] at hu
  exact honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime S adm hv hu huv

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
