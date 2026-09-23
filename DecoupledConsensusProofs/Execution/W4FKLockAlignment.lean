module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.CanonicalRegimeProducer

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 finality kernel — the record-lock / height-read alignment

This leaf closes wave A2 of the finality-kernel plan (judgment branches
`w4-fk-judge`, §Q3). It restates the two lock-alignment producers parked in
`HealingSurface/CanonicalRegimeProducerRun.lean` over the named runtime.

The parked declarations stalled on one identifier, the erased
`recordLock_finalityEmission_before`. Its named twin
`recordLock_finalityEmission_before_migration`
(`HealingSurface/MigrationResidualsRun.lean`) is live and public, so the two
statements proof with no new hypothesis: `proposedBlock S rho (opening r)` is
replaced by a bound named proposal `P0` with
`proposedBlockAt … = some P0`, and `derived_state` by
`Protocol.derive_named`.

Protocol content. A node's finality record stores, per height, a locked
target. A lock at a height was written by some earlier honest tick of that
same node, and that tick emitted an attestation carrying the finality pair at
the same height. Once the height is above the boundary frontier, the causal
source of any such pair lies on the carrier opening chain, so its target is the
height's canonical target. The same argument applied to the round's own action
attestation covers the second half of the alignment.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Confirmation time is monotone in the slot. Local copy: the producer file's
own copy is `private`. -/
private theorem confirmation_time_mono_lock_alignment
    (E : Env V) {s u : Slot} (hsu : s ≤ u) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E u := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hsu 1)

/-- At every canonical height above the boundary frontier, every stored lock
and every same-action finality pair uses that height's canonical target. -/
theorem CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
    (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hfb : BelowOneThird S rho.honest)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {H : Height} {P0 W : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hW : NamedBlock.Preceq W P0)
    (hWheight : (Protocol.derive_named S.E S.cfg W).h = H)
    (habove : honestHMaxAt S rho (S.a q0) < H) :
    ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        H (Protocol.derive_named S.E S.cfg W).T_h.root := by
  have hfinality : FinalityTargetHeightSource S rho :=
    finalityTargetHeightSource_of_admissible S adm hfb
  intro v hv
  constructor
  · intro X hlock
    obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
    have hlockN : (rho.stateBefore S n v).record.legacy.lock H = some X := by
      rw [← hn]
      exact hlock
    obtain ⟨i, hi, ta, a, hevent, hemitted, hpair⟩ :=
      recordLock_finalityEmission_before_migration S rho v n hlockN
    have haEmit : rho.emits S v (.attest a) ta :=
      ⟨i, hevent, hemitted⟩
    have haHonest : a.val_index ∈ rho.honest := by
      rw [(Proofs.Optimistic.emits_attest_shape S haEmit).1]
      exact hv
    exact finalityPairTarget_eq_canonicalTarget
      S adm hfinality hround hP0 hW hWheight habove haHonest
        (by simpa only [(Proofs.Optimistic.emits_attest_shape S haEmit).1] using haEmit)
        (le_of_lt (hbefore i _ hi hevent)) hpair
  · intro p hfp hpHeight
    have hactionHor : S.a r ≤ rho.horizon := by
      have hmono : Protocol.confirmation_time S.E
          (S.hc.opening_slot r) ≤ Protocol.confirmation_time S.E
            (S.hc.opening_slot r + 2) :=
        confirmation_time_mono_lock_alignment S.E (Nat.le_add_right _ 2)
      have ha : S.a r ≤ Protocol.confirmation_time S.E
          (S.hc.opening_slot r + 2) := by
        simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hmono
      exact ha.trans hround.inHorizon
    have haEmit := honest_emits_exact_actionAttestationAt
      S adm hv r hactionHor
    rcases p with ⟨height, target⟩
    change height = H at hpHeight
    subst height
    have haHonest :
        (actionAttestationAt S rho v r).val_index ∈ rho.honest := by
      rw [(actionAttestationAt_shape S rho v r).1]
      exact hv
    have haEmit' : rho.emits S
        (actionAttestationAt S rho v r).val_index
        (.attest (actionAttestationAt S rho v r)) (S.a r) := by
      rw [(actionAttestationAt_shape S rho v r).1]
      exact haEmit
    exact finalityPairTarget_eq_canonicalTarget
      S adm hfinality hround hP0 hW hWheight habove
        (a := actionAttestationAt S rho v r) (ta := S.a r)
        (target := target) haHonest haEmit'
        (show S.a r ≤ S.a r from le_rfl) hfp

/-- The carrier-opening instance of the canonical-height lock alignment. -/
theorem CanonicalRegimeRoundAt.successorTargetLockAlignment_of_aboveBoundary
    (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hfb : BelowOneThird S rho.honest)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h) :
    ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0).T_h.root :=
  CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
      S adm hfb hround hP0 (Proofs.NamedAncestry.named_self P0) rfl habove

#print axioms CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
#print axioms CanonicalRegimeRoundAt.successorTargetLockAlignment_of_aboveBoundary

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
