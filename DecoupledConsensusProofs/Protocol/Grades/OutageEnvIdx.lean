module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IdxDriverSteps
public import DecoupledConsensusProofs.Execution.IdxDriverHelpers
public import DecoupledConsensusProofs.Protocol.Grades.GuardedGradeHelpers
public import DecoupledConsensusProofs.Protocol.Grades.ReadyHeadReturnIndices
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Store.RawSource
public import DecoupledConsensusProofs.Protocol.Handlers.PublicCutBody
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityCarrier
public import DecoupledConsensusProofs.Protocol.Schedule.HeldSkipProducers
public import DecoupledConsensusProofs.Execution.ViabilityHistoryIndices
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JustificationHistoryIndices
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore
public import DecoupledConsensusProofs.Protocol.Handlers.HandlerAdmissionGuards
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.HeldJustificationHistoryIdx
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageEnv
open DecoupledConsensusModel
open Internal Execution Internal.NamedOutageEntry DecoupledConsensusModel.Protocol Protocol
open Internal.NamedStableChainOutage
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule fact: the G2 domain read of a positive round is nonnegative -/

/-- `domain r.g2 = 4Δ·(rR) − Δ`, and `rR ≥ R ≥ 2` once `0 < r`, so the
domain read is at least `7Δ > 0`. Only `HealConfig.R_ge_two` is needed. -/
theorem domain_g2_nonneg (S : Setup V) {r : Round} (hr : 0 < r) :
    0 ≤ domain S.E S.hc r .g2 := by
  have hnat : (2 : Nat) ≤ r * S.hc.R := by
    have h1 : (1 : Nat) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ hr
    rw [one_mul] at h1
    exact le_trans S.hc.R_ge_two h1
  have hcast : (2 : Time) ≤ ((r * S.hc.R : Nat) : Time) := by exact_mod_cast hnat
  have heq : domain S.E S.hc r .g2 =
      S.E.Δ * (4 * ((r * S.hc.R : Nat) : Time) - 1) := by
    unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.opening DecoupledConsensusModel.Protocol.Phase.domainOffset
      Protocol.proposal_time Env.t Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  have hb : (0 : Time) ≤ 4 * ((r * S.hc.R : Nat) : Time) - 1 := by
    have h4 : (4 : Time) * 2 ≤ 4 * ((r * S.hc.R : Nat) : Time) :=
      Int.mul_le_mul_of_nonneg_left hcast (by norm_num)
    have h18 : (1 : Time) ≤ 4 * 2 := by norm_num
    exact sub_nonneg.mpr (h18.trans h4)
  rw [heq]
  exact Int.mul_nonneg S.E.Δ_pos.le hb

/-! ## The outage instantiation of the driver -/




/-! ## Direct public-clause projection of one layer-A witness -/

/-- The layer-A history directly excludes height and finality conflicts with
its own witness. The outer outage proof still has to place the protected block
on this witness chain. -/
theorem noHonestConflictAbove_of_layerA_witness
    (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (core : NamedAdmissibleCore S rho) (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdx S rho (boundaryIdx rho b0) C) :
    NoHonestConflictAbove S rho b0 C.erase := by
  have hCrun : NamedRun.blockInRun S rho C := hhistory.1.1
  constructor
  · intro Pn hPn hPnErase a t ha hemit ht h root timeout hpair entry hentry hroot
    obtain ⟨i, hi, himem⟩ := hemit
    have hibound : i < boundaryIdx rho b0 :=
      tick_index_lt_boundaryIdx rho core.sorted hi (by
        simpa only [NamedEvent.time] using ht)
    obtain ⟨source, entry', _, _, hentryRun, _, _, _, _, _, _, _, _, _, _, _,
        hentryRoot, hentryC⟩ :=
      hhistory.1.2.2.1 i a.val_index t a ha hi himem hibound
        h root timeout hpair
    have hPnRoot : Pn.root = C.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hPnErase
    have hPnC : Pn = C :=
      core.toNamedRootCollisionFree.root_injective Pn C hPn hCrun Pn C
        (Or.inl (Proofs.NamedAncestry.named_self Pn))
        (Or.inr (Proofs.NamedAncestry.named_self C)) hPnRoot
    have hentryEq : entry = entry' :=
      core.toNamedRootCollisionFree.root_injective entry C hentry hCrun entry entry'
        (Or.inl (Proofs.NamedAncestry.named_self entry)) (Or.inr hentryC)
        (hroot.trans hentryRoot.symm)
    rw [hPnC, hentryEq]
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    exact Or.inr hentryC
  · intro Pn hPn hPnErase a t ha hemit ht h root hpair entry hentry hroot
    obtain ⟨i, hi, himem⟩ := hemit
    have hibound : i < boundaryIdx rho b0 :=
      tick_index_lt_boundaryIdx rho core.sorted hi (by
        simpa only [NamedEvent.time] using ht)
    obtain ⟨H, K, _, _, _, hKrun, _, _, _, _, _, _, _, _, _, _, hKroot, hKC⟩ :=
      hhistory.1.2.1 i a.val_index t a ha hi himem hibound ⟨h, root⟩ hpair
    have hPnRoot : Pn.root = C.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hPnErase
    have hPnC : Pn = C :=
      core.toNamedRootCollisionFree.root_injective Pn C hPn hCrun Pn C
        (Or.inl (Proofs.NamedAncestry.named_self Pn))
        (Or.inr (Proofs.NamedAncestry.named_self C)) hPnRoot
    have hentryEq : entry = K :=
      core.toNamedRootCollisionFree.root_injective entry C hentry hCrun entry K
        (Or.inl (Proofs.NamedAncestry.named_self entry)) (Or.inr hKC)
        (hroot.trans hKroot)
    rw [hPnC, hentryEq]
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    exact Or.inr hKC

/-- Any named ancestor of the layer-A witness has the same no-conflict
property. The caller supplies the protected representative and its position on
the witness chain. -/
theorem noHonestConflictAbove_of_layerA
    (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (core : NamedAdmissibleCore S rho) (C Pn : NamedBlock V)
    (hhistory : LayerAJointHistoryIdx S rho (boundaryIdx rho b0) C)
    (hPn : NamedRun.blockInRun S rho Pn) (hPnC : NamedBlock.Preceq Pn C) :
    NoHonestConflictAbove S rho b0 Pn.erase := by
  have hbase := noHonestConflictAbove_of_layerA_witness S rho b0 core C hhistory
  have hCrun : NamedRun.blockInRun S rho C := hhistory.1.1
  have compatible_of_witness {entry : NamedBlock V}
      (hentry : NamedRun.blockInRun S rho entry)
      (hcompat : NamedBlock.compatible C entry = true) :
      NamedBlock.compatible Pn entry = true := by
    simp only [NamedBlock.compatible, Bool.or_eq_true] at hcompat ⊢
    rcases hcompat with hCentry | hentryC
    · exact Or.inl
        (IdxDriverHelpers.named_preceq_trans hPnC hCentry)
    · have hraw := Block.preceq_linear
          (Proofs.NamedWire.erase_preceq hPnC) (Proofs.NamedWire.erase_preceq hentryC)
      rcases hraw with hPnEntry | hEntryPn
      · exact Or.inl
          (JointHistoryProducersTime.named_of_erase_preceq
            S rho core hPn hentry hPnEntry)
      · exact Or.inr
          (JointHistoryProducersTime.named_of_erase_preceq
            S rho core hentry hPn hEntryPn)
  constructor
  · intro Pn' hPn' hErase a t ha hemit ht h root timeout hpair entry hentry hroot
    have hrootEq : Pn'.root = Pn.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hErase
    have heq : Pn' = Pn :=
      core.toNamedRootCollisionFree.root_injective Pn' Pn hPn' hPn Pn' Pn
        (Or.inl (Proofs.NamedAncestry.named_self Pn'))
        (Or.inr (Proofs.NamedAncestry.named_self Pn)) hrootEq
    rw [heq]
    exact compatible_of_witness hentry
      (hbase.1 C hCrun rfl a t ha hemit ht h root timeout hpair entry hentry hroot)
  · intro Pn' hPn' hErase a t ha hemit ht h root hpair entry hentry hroot
    have hrootEq : Pn'.root = Pn.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hErase
    have heq : Pn' = Pn :=
      core.toNamedRootCollisionFree.root_injective Pn' Pn hPn' hPn Pn' Pn
        (Or.inl (Proofs.NamedAncestry.named_self Pn'))
        (Or.inr (Proofs.NamedAncestry.named_self Pn)) hrootEq
    rw [heq]
    exact compatible_of_witness hentry
      (hbase.2 C hCrun rfl a t ha hemit ht h root hpair entry hentry hroot)



#print axioms domain_g2_nonneg
#print axioms noHonestConflictAbove_of_layerA_witness
#print axioms noHonestConflictAbove_of_layerA
end DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageEnv

end
