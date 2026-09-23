module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Named recovery-height NJ and head producers

The erased `NjGap` induction is not a bridge for the named runtime. This
module repeats the small chain induction over `derive_named`, then lifts it to
the retained bodies behind the contract reads used by a round action.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace NjGap

omit [Fintype V] in
private theorem named_fold_nj (rows : List (NamedAttestation V))
    (st : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st).nj = st.nj := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact process_attestation_nj st _

private theorem named_fold_h (rows : List (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      {st with s := geometry.slot}).h = st.h :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.1

private theorem named_fold_h_j (rows : List (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      {st with s := geometry.slot}).h_j = st.h_j :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.2.2.2.1

private theorem named_fold_h_F (rows : List (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      {st with s := geometry.slot}).h_F = st.h_F :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.2.2.2.2.2

/-- The named derivation carries the same entry witness as the chain derivation.

The witness is over `derive_named`; it does not compare that state with an
erased derivation at `B.erase`.
-/
theorem njEntry_derive_named (E : Env V) (cfg : HeightConfig) :
    ∀ B : NamedBlock V, NjEntry cfg (derive_named E cfg B) := by
  intro B
  induction B with
  | genesis => exact njEntry_initial cfg
  | node parent slot root votes support rows proposer ih =>
      rw [BlockProcessingDefaults.derive_named_node]
      unfold named_transition transition_rows
      rw [Protocol.process_height_events_eq]
      split_ifs
      · exact ⟨_, Nat.le_refl _, rfl⟩
      · exact ⟨_, Nat.le_refl _, rfl⟩
      · refine ⟨ih.choose, ?_, ?_⟩
        · have hmono := NjGap.le_afterFin_h_F E
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
              (NamedBlock.node parent slot root votes support rows proposer).erase
              (NamedBlock.node parent slot root votes support rows proposer).attestations)
          have hfoldF :
              (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
                (NamedBlock.node parent slot root votes support rows proposer).erase
                (NamedBlock.node parent slot root votes support rows proposer).attestations).h_F =
                (derive_named E cfg parent).h_F := by
            unfold fold_rows
            exact named_fold_h_F _ _ _
          rw [hfoldF] at hmono
          exact Nat.le_trans ih.choose_spec.1 hmono
        · rw [Protocol.afterFin_nj, Protocol.afterFin_h]
          simp only [fold_rows, named_fold_nj, named_fold_h]
          exact ih.choose_spec.2

/-- A named body at a capped recovery height has its NJ latch set. -/
theorem nj_of_cap_named (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V} {h_F0 H : Height}
    (hrec : RecoveryHeight cfg h_F0 H)
    (hcap : (derive_named E cfg B).h_F ≤ h_F0)
    (hh : (derive_named E cfg B).h = H) :
    (derive_named E cfg B).nj = true := by
  obtain ⟨hF', hle, heq⟩ := njEntry_derive_named E cfg B
  have hle' : hF' ≤ h_F0 := hle.trans hcap
  rw [heq, hh]
  exact nonjustifiable_of_le hle' (nonjustifiable_of hrec.1 hrec.2)

/-- A named capped chain cannot justify its recovery height. -/
theorem h_j_ne_recovery_height_named (E : Env V) (cfg : HeightConfig)
    {h_F0 H : Height}
    (hrec : RecoveryHeight cfg h_F0 H) :
    ∀ B : NamedBlock V,
      (∀ C : NamedBlock V, NamedBlock.Preceq C B →
        (derive_named E cfg C).h_F ≤ h_F0) →
      (derive_named E cfg B).h_j ≠ H := by
  intro B
  induction B with
  | genesis =>
      intro _
      have hz : (derive_named E cfg (NamedBlock.genesis : NamedBlock V)).h_j = 0 := rfl
      rw [hz]
      have hpos : 0 < H := (Nat.zero_le _).trans_lt
        (NjGap.lt_of_recoveryHeight hrec)
      exact Nat.ne_of_lt hpos
  | node parent slot root votes support rows proposer ih =>
      intro hcap
      have hcapp : ∀ C : NamedBlock V, NamedBlock.Preceq C parent →
          (derive_named E cfg C).h_F ≤ h_F0 := by
        intro C hC
        exact hcap C (Proofs.NamedAncestry.named_extend slot root votes support rows proposer hC)
      rw [BlockProcessingDefaults.derive_named_node]
      unfold named_transition transition_rows
      rw [Protocol.process_height_events_eq]
      split_ifs with h1 h2
      · rw [Protocol.advance_height_h_j]
        intro hcontra
        change (Protocol.afterFin E
          (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
            (NamedBlock.node parent slot root votes support rows proposer).erase
            (NamedBlock.node parent slot root votes support rows proposer).attestations)).h = H
          at hcontra
        have hh : (derive_named E cfg parent).h = H := by
          rw [Protocol.afterFin_h] at hcontra
          simpa only [fold_rows, named_fold_h] using hcontra
        have hnj : targetReady E (Protocol.afterFin E
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
              (NamedBlock.node parent slot root votes support rows proposer).erase
              (NamedBlock.node parent slot root votes support rows proposer).attestations)) =
            false := by
          refine targetReady_eq_false_of_nj E ?_
          rw [Protocol.afterFin_nj]
          simpa only [fold_rows, named_fold_nj] using
            (nj_of_cap_named (E := E) (cfg := cfg) hrec
              (hcapp parent (Proofs.NamedAncestry.named_self parent)) hh)
        rw [hnj] at h1
        simp at h1
      · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j]
        simpa only [fold_rows, named_fold_h_j] using ih hcapp
      · rw [Protocol.afterFin_h_j]
        simpa only [fold_rows, named_fold_h_j] using ih hcapp

end NjGap

namespace HealingSurface

open Protocol
open NamedActionReads



private theorem action_read_invariant (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
  apply Proofs.NamedConfirmationMembership.invariant_update
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1

theorem actionHeadWith_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing ∈
      (rho.storeBeforeTime S v (S.a r)).T := by
  let n := actionStoreAt S rho v r
  let gc := NamedProfile.gradeContract n.cache
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    action_read_invariant S rho v r
  have hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈ n.st.T :=
    Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
  have hanchor := Proofs.NamedConfirmationMembership.runtime_anchor_mem n.cache
    S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s) hroot
  have hhead : Protocol.get_head_with gc S.E S.hc n.st.core.toHealing
      (n.st.core.toHealing.pool n.st.core.s)
      ((n.st.core.toHealing.pool n.st.core.s).filter
        (fun u => Protocol.resolved n.st.core.toHealing.T u = true)) n.st.core.s ∈ n.st.T :=
    NamedProposalParent.get_head_with_mem gc S.E S.hc n.st.core.toHealing _ _ _ hanchor
  have hT : n.st.T = (rho.storeBeforeTime S v (S.a r)).T := rfl
  rw [← hT]
  exact hhead




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
