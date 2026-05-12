import DecoupledConsensus.Store.Proof.Conditional

namespace DecoupledConsensus

/-! # Store Properties

Clean statement layer for the Section 3 store results.

The executable definitions live under `Store.Model`. The proof scripts live
under `Store.Proof`. This file gives the public theorem surface as small
`Prop`-valued statement definitions plus theorem aliases whose bodies delegate
to the proof modules.

The order-independence statements below are deliberately the proved
extensional form (`OrderEquivalent`). They should not be read as the stronger
TeX claim that arbitrary valid processing orders over the same block set
produce equivalent stores; that replay/order machinery is not formalized yet.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-! ## Unconditional Store Properties -/

/-- Store justification height is monotone across future execution. -/
def HjMonotoneStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n}, Future S T → S.hj ≤ T.hj

theorem hj_monotone_property : HjMonotoneStatement n := by
  intro S T hFuture
  exact future_hj_mono hFuture

/-- Store justification keys are monotone across future execution. -/
def KeyMonotoneStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n}, Future S T → KeyLE S.hj S.J T.hj T.J

theorem key_monotone_property : KeyMonotoneStatement n := by
  intro S T hFuture
  exact future_key_mono hFuture

/-- Once store finality reaches `S.F`, every future finalized root descends
    from it. -/
def FinalityIrreversibilityStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n}, Future S T → S.F ≼ T.F

theorem finality_irreversibility_property :
    FinalityIrreversibilityStatement n := by
  intro S T hFuture
  exact future_F_ancestor hFuture

/-- Reachable stores maintain `F ≼ J`. -/
def FAncestorJStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S → S.F ≼ S.J

theorem f_ancestor_j_property : FAncestorJStatement n := by
  intro S hS
  exact reachable_F_ancestor_J hS

/-- Reachable stores keep the finalized root viable. -/
def FViableStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S → S.isViableBool S.F = true

theorem f_viable_property : FViableStatement n := by
  intro S hS
  exact reachable_F_viableBool hS

/-- The set-valued executable `getConfirmed` is nonempty on reachable stores
    and every output satisfies the candidate predicate. -/
def GetConfirmedTotalStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S →
    ∃ B : Block n, B ∈ S.getConfirmed ∧ ConfirmedCandidate S B

theorem getConfirmed_total_property : GetConfirmedTotalStatement n := by
  intro S hS
  exact reachable_getConfirmed_total hS

/-- Future confirmed outputs always descend from the earlier finalized root. -/
def ForkChoiceConsistencyStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n} {B : Block n},
    Reachable S → Future S T → B ∈ T.getConfirmed → S.F ≼ B

theorem forkChoice_consistency_property :
    ForkChoiceConsistencyStatement n := by
  intro S T B hS hFuture hB
  exact future_getConfirmed_descends_from_F hS hFuture hB

/-- Reachable stores satisfy the no-high-justification invariant. -/
def NoHighJustificationsStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S → NoHighJustifications S

theorem noHigh_justifications_property :
    NoHighJustificationsStatement n := by
  intro S hS
  exact reachable_noHighJustifications hS

/-! ## Accountable Store Properties -/

/-- A finalization certificate and a later processed justification are
    compatible unless accountable slashability has already occurred. -/
def CertChainStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S : Store n} {F C : Block n} {h_f h : ℕ},
        (rF : FinalizationRecord F h_f) →
        (rJ : JustificationRecord S C h) →
        rF.IdInjectiveAgainstStore S →
        h_f ≤ h →
        F ~ C

theorem certChain_property {f : ℕ} :
    CertChainStatement n f := by
  intro hn hNoSlash S F C h_f h rF rJ hId hle
  exact certchain_record_compatible hn hNoSlash rF rJ hId hle

/-- Processed-finalization upgrade: after processing a descriptor `(F, h_f)`,
    future store roots descend from `F`. -/
def UpgradeStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S T : Store n},
        Reachable S → Future S T →
          ∀ {F : Block n} {h_f : ℕ},
            (rF : FinalizationRecord F h_f) →
            ProcessedJustification S F h_f →
            rF.IdInjectiveAgainstStore T →
            F ≼ T.J

theorem upgrade_property {f : ℕ} :
    UpgradeStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f rF hProc hId
  exact upgrade_of_processed hn hNoSlash hS hFuture rF hProc hId

/-- A processed finalized checkpoint remains viable in future stores. -/
def FinalizedViableStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S T : Store n},
        Reachable S → Future S T →
          ∀ {F : Block n} {h_f : ℕ},
            (rF : FinalizationRecord F h_f) →
            ProcessedJustification S F h_f →
            rF.IdInjectiveAgainstStore T →
            T.isViableBool F = true

theorem finalized_viable_property {f : ℕ} :
    FinalizedViableStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f rF hProc hId
  exact future_finalized_viableBool_of_processedJustification
    hn hNoSlash hS hFuture hId rF.chain rF.final_state
    rF.certificate hProc

/-- Local finality update acceptance, stated at the exposed store mutator. -/
def FinalityUpdateAcceptanceStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S : Store n}, Reachable S →
        ∀ {F' : Block n} {h_f : ℕ},
          (rF : FinalizationRecord F' h_f) →
          ProcessedJustification S F' h_f →
          rF.IdInjectiveAgainstStore S →
          S.F ≼ F' ∧ S.F ≠ F' →
          (S.updateFinalized F').F = F'

theorem finality_update_acceptance_property {f : ℕ} :
    FinalityUpdateAcceptanceStatement n f := by
  intro hn hNoSlash S hS F' h_f rF hProc hId hStrict
  exact updateFinalized_accepts_processed_finalization
    hn hNoSlash hS rF hProc hId hStrict

/-- Lock-in for any executable `getConfirmed` output. -/
def LockInStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S T : Store n},
        Reachable S → Future S T →
          ∀ {F B : Block n} {h_f : ℕ},
            (rF : FinalizationRecord F h_f) →
            ProcessedJustification S F h_f →
            rF.IdInjectiveAgainstStore T →
            B ∈ T.getConfirmed →
            F ≼ T.J ∧ T.isViableBool F = true ∧ F ≼ B

theorem lockIn_property {f : ℕ} :
    LockInStatement n f := by
  intro hn hNoSlash S T hS hFuture F B h_f rF hProc hId hB
  exact lockin_of_processed hn hNoSlash hS hFuture rF hProc hId hB

/-! ## Proved Extensional Order-Independence Surface -/

/-- Order-equivalent stores have the same `getConfirmed` membership. -/
def OrderEquivalentGetConfirmedStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n} {B : Block n},
    OrderEquivalent S T → (B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed)

theorem orderEquivalent_getConfirmed_property :
    OrderEquivalentGetConfirmedStatement n := by
  intro S T B hEq
  exact orderindep_getConfirmed hEq

/-- Order-equivalent stores have the same viable-tree membership. -/
def OrderEquivalentViableTreeStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n} {B : Block n},
    OrderEquivalent S T → (B ∈ S.viableTree ↔ B ∈ T.viableTree)

theorem orderEquivalent_viableTree_property :
    OrderEquivalentViableTreeStatement n := by
  intro S T B hEq
  exact orderindep_viableTree hEq

end Store

end DecoupledConsensus
