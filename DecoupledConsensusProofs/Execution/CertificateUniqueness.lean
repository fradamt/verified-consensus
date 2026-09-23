module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Objects.Weights
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Bridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Run certificate authenticity and uniqueness

This module proves the run-level facts needed to compare certificate targets.
The proof uses execution authenticity to recover honest emissions, converts a
certificate's honest quorum into a completable target, and applies per-height
completability under `BelowOneThird`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every object listed by a run was processed by the node that received it. -/
theorem exists_processes_of_mem_objects (S : Setup V) (rho : Run V) {o : Object V}
    (h : o ∈ NamedRun.objects rho) :
    ∃ (u : V) (t : Time), NamedRun.processes S rho u o t := by
  obtain ⟨e, hmem, he⟩ := List.mem_filterMap.mp h
  cases e with
  | tick u t =>
      have hnone : (none : Option (Object V)) = some o := he
      exact absurd hnone (by simp)
  | deliver u p t =>
      have heq : p = o := Option.some.inj he
      subst heq
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact ⟨u, t, Or.inr ⟨i, hi⟩⟩

omit [Fintype V] in
/-- A named row carried by a chain, up to erasure, is a member of the chain's
erased evidence set. The named fold nests the same way `chain_attestations`
does (parent first, own rows last), so the ordinary structural monotonicity
and own-row membership lemmas carry it across at every level. -/
private theorem mem_named_chain_attestations_erase {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ Protocol.named_chain_attestations B) :
    a.erase ∈ chain_attestations B.erase := by
  induction B with
  | genesis =>
      have h0 : a ∈ (∅ : Finset (NamedAttestation V)) := ha
      exact absurd h0 (by simp)
  | node p s r votes support rows proposer ih =>
      have hu : a ∈ Protocol.named_chain_attestations p ∪ rows.toFinset := ha
      rw [Finset.mem_union, List.mem_toFinset] at hu
      rcases hu with hu | hu
      · exact Protocol.chain_attestations_mono
          (Protocol.preceq_node p.erase s r votes support (rows.map NamedAttestation.erase)
            proposer) (ih hu)
      · exact Protocol.mem_chain_attestations_of_mem (List.mem_map.mpr ⟨a, hu, rfl⟩)

/-- A run attestation in an honest name was emitted by that validator, up to
the erasure some carried row is retrieved at. The objects disjunct hands back
the row itself (`rfl`); the carried disjunct only recovers a row whose erasure
matches, which is `Proofs.NamedStoreBridge.carriedByHonest_of_runBlock`'s own shape. -/
theorem runAttestation_emits (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {a : NamedAttestation V} (ha : Internal.HealingSurface.RunAttestation S rho a)
    (hh : a.val_index ∈ rho.honest) :
    ∃ (row : NamedAttestation V) (t : Time), row.erase = a.erase ∧
      rho.emits S a.val_index (Object.attest row) t := by
  rcases ha with hobj | ⟨B, hB, hmem⟩
  · obtain ⟨u, t, hproc⟩ := exists_processes_of_mem_objects S rho hobj
    obtain ⟨t', -, hem⟩ :=
      hadm.toNamedAdmissibleCore.toNamedUnforgeable.unforgeable
        u (Object.attest a) t hproc a.val_index hh rfl
    exact ⟨a, t', rfl, hem⟩
  · exact Proofs.NamedStoreBridge.carriedByHonest_of_runBlock S hadm.toNamedAdmissibleCore hB a.erase
      (mem_named_chain_attestations_erase hmem) hh

/-- A certificate is completable by its honest signers. -/
theorem completable_of_certificate (S : Setup V) {rho : Run V}
    (hadm : Admissible S rho) {h : Height} {T : BlockId}
    (hc : Internal.HealingSurface.Certificate S rho h T) :
    Internal.HealingSurface.Completable S rho h T := by
  obtain ⟨Q, hQ, hsig⟩ := hc
  refine ⟨Q ∩ rho.honest, Finset.inter_subset_right, quorum_meets_set S.E hQ, ?_⟩
  intro v hv
  obtain ⟨hvQ, hvh⟩ := Finset.mem_inter.mp hv
  obtain ⟨a, hra, hav, hhp⟩ := hsig v hvQ
  obtain ⟨row, t, herase, hem⟩ := runAttestation_emits S hadm hra (by rw [hav]; exact hvh)
  rw [hav] at hem
  refine ⟨row, t, hem, ?_⟩
  have hT : row.erase.height_pair = HeightPair.target h T := by
    rw [herase]
    simp [NamedAttestation.erase, hhp, NamedHeightPair.erase]
  exact Or.inl hT

/-- Two certificates at one height have the same target under `BelowOneThird`. -/
theorem certificateTarget_unique (S : Setup V) {rho : Run V}
    (hadm : Admissible S rho) (hfb : BelowOneThird S rho.honest)
    (h : Height) (T T' : BlockId)
    (hT : Internal.HealingSurface.Certificate S rho h T)
    (hT' : Internal.HealingSurface.Certificate S rho h T') : T = T' :=
  perHeightCompletability S hfb h T T'
    (completable_of_certificate S hadm hT) (completable_of_certificate S hadm hT')

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
