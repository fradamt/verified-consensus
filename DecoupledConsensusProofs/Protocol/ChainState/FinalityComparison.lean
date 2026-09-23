module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FinalizationBridge
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.ChainState.Evidence

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem own_row_erase_mem (B : NamedBlock V) (a : NamedAttestation V)
    (ha : a ∈ B.attestations) : a.erase ∈ chain_attestations B.erase := by
  cases B with
  | genesis => simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer =>
    apply Protocol.mem_chain_attestations_of_mem
    exact List.mem_map.mpr ⟨a, ha, rfl⟩

omit [Fintype V] in
private theorem on_chain_erase_mem {tip carrier : NamedBlock V} {a : NamedAttestation V}
    (hcarrier : NamedBlock.Preceq carrier tip) (ha : a ∈ carrier.attestations) :
    a.erase ∈ chain_attestations tip.erase :=
  Protocol.chain_attestations_mono (Proofs.NamedWire.erase_preceq hcarrier)
    (own_row_erase_mem carrier a ha)

omit [Fintype V] in
private theorem matching_finality_e1 (a b : NamedAttestation V)
    (h : Height) (entry finalized : BlockId)
    (hv : a.val_index = b.val_index)
    (hm : a.height_pair.matchesEntry h entry = true)
    (hf : b.finality_pair = some ⟨h, finalized⟩) (hne : entry ≠ finalized) :
    Protocol.Slashable a.erase b.erase := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height root timeout =>
    have heq : height = h ∧ root = entry := by
      simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
    rcases heq with ⟨rfl, rfl⟩
    cases timeout <;>
      simp [Protocol.Slashable, Protocol.slashable,
        Protocol.e1Slashable, Protocol.e1Fields,
        Protocol.conflictsWithFinality, Protocol.sameValidator,
        NamedAttestation.erase, NamedHeightPair.erase, hp, hf, hv, hne]

theorem finalized_preceq_of_height_lt
    (S : Setup V) (rho : NamedRun V) (C D : NamedBlock V)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
    (hroot : NamedRootCollisionFree S rho)
    (hC : NamedRun.blockInRun S rho C) (hD : NamedRun.blockInRun S rho D)
    (hlt : (derive_named S.E S.cfg D).h_F < (derive_named S.E S.cfg C).h) :
    Block.Preceq (derive_named S.E S.cfg D).F C.erase := by
  by_cases hz : (derive_named S.E S.cfg D).h_F = 0
  · rw [NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg D hz]
    exact Protocol.preceq_genesis C.erase
  · obtain ⟨F, hFD, hFE, Qf, hQf, hwf⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg D hz
    obtain ⟨X, hXC, _hXheight, Qc, hQc, hwc⟩ :=
      NamedFinalityCertificates.height_crossing S.E S.cfg C
        (derive_named S.E S.cfg D).h_F (Nat.one_le_iff_ne_zero.mpr hz) hlt
    by_cases hroots : X.root = F.root
    · have hXF : X = F :=
        hroot.root_injective C D hC hD X F (Or.inl hXC) (Or.inr hFD) hroots
      rw [← hFE, ← hXF]
      exact Proofs.NamedWire.erase_preceq hXC
    · exfalso
      apply hsb C D hC hD
      refine ⟨Qc ∩ Qf, quorum_intersection S.E hQc hQf, ?_⟩
      intro signer hsigner
      obtain ⟨hc, hf⟩ := Finset.mem_inter.mp hsigner
      obtain ⟨carrierA, a, hcarrierA, ha, hav, hamatch⟩ := hwc signer hc
      obtain ⟨carrierB, b, hcarrierB, hb, hbv, hbfinal⟩ := hwf signer hf
      refine ⟨a.erase, on_chain_erase_mem hcarrierA ha,
        b.erase, on_chain_erase_mem hcarrierB hb, ?_, ?_, ?_⟩
      · exact hav
      · exact hbv
      · exact matching_finality_e1 a b (derive_named S.E S.cfg D).h_F X.root F.root
          (hav.trans hbv.symm) hamatch hbfinal hroots

/-! The compatibility form used by the height-regime consumers. -/

/-- Named twin of the archived `no_off_can_finalization_of_run`. -/
theorem named_no_off_can_finalization
    (S : Setup V) (rho : NamedRun V) (C D : NamedBlock V)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
    (hroot : NamedRootCollisionFree S rho)
    (hC : NamedRun.blockInRun S rho C)
    (hD : NamedRun.blockInRun S rho D)
    (hlt : (derive_named S.E S.cfg D).h_F <
      (derive_named S.E S.cfg C).h) :
    Block.compatible (derive_named S.E S.cfg D).F C.erase = true := by
  have h := finalized_preceq_of_height_lt S rho C D hsb hroot hC hD hlt
  simp only [Block.compatible, Bool.or_eq_true]
  exact Or.inl h


end DecoupledConsensusModel.Proofs.NamedFinalizationBridge

end
