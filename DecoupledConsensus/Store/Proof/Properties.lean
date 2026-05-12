import DecoupledConsensus.Store.Properties
import DecoupledConsensus.Store.Proof.Conditional

namespace DecoupledConsensus

/-! # Store Property Proof Facade

This module proves the statement definitions from `Store.Properties` by
delegating to the proof modules. It is intentionally thin: theorem statements
stay readable in `Store.Properties`, while proof scripts remain under
`Store.Proof`.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-! ## Unconditional Store Properties -/

theorem hj_monotone_property : HjMonotoneStatement n := by
  intro S T hFuture
  exact future_hj_mono hFuture

theorem key_monotone_property : KeyMonotoneStatement n := by
  intro S T hFuture
  exact future_key_mono hFuture

theorem finality_irreversibility_property :
    FinalityIrreversibilityStatement n := by
  intro S T hFuture
  exact future_F_ancestor hFuture

theorem f_ancestor_j_property : FAncestorJStatement n := by
  intro S hS
  exact reachable_F_ancestor_J hS

theorem f_viable_property : FViableStatement n := by
  intro S hS
  exact reachable_F_viableBool hS

theorem getConfirmed_total_property : GetConfirmedTotalStatement n := by
  intro S hS
  exact ⟨reachable_getConfirmed_nonempty hS, fun hB => getConfirmed_candidate hB⟩

theorem forkChoice_consistency_property :
    ForkChoiceConsistencyStatement n := by
  intro S T B hS hFuture hB
  exact future_getConfirmed_descends_from_F hS hFuture hB

theorem noHigh_justifications_property :
    NoHighJustificationsStatement n := by
  intro S hS
  exact reachable_noHighJustifications hS

/-! ## Accountable Store Properties -/

theorem certChain_property {f : ℕ} :
    CertChainStatement n f := by
  intro hn hNoSlash S F C h_f h rF rJ hId hle
  exact certchain_record_compatible hn hNoSlash rF rJ hId hle

theorem certChain_strict_property {f : ℕ} :
    CertChainStrictStatement n f := by
  intro hn hNoSlash S F C h_f h rF rJ hId hpos hlt
  exact certchain_record_strict_of_positive
    hn hNoSlash rF rJ hId hpos hlt

theorem upgrade_property {f : ℕ} :
    UpgradeStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f rF hProc hId
  exact upgrade_of_processed hn hNoSlash hS hFuture rF hProc hId

theorem finalized_viable_property {f : ℕ} :
    FinalizedViableStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f rF hProc hId
  exact future_finalized_viableBool_of_processedJustification
    hn hNoSlash hS hFuture hId rF.chain rF.final_state
    rF.certificate hProc

theorem finality_update_acceptance_property {f : ℕ} :
    FinalityUpdateAcceptanceStatement n f := by
  intro hn hNoSlash S hS F' h_f rF hProc hId hStrict
  exact updateFinalized_accepts_processed_finalization
    hn hNoSlash hS rF hProc hId hStrict

theorem finality_update_descends_property {f : ℕ} :
    FinalityUpdateDescendsStatement n f := by
  intro hn hNoSlash S hS F' h_f rF hProc hId hAlreadyOrStrict
  exact updateFinalized_descends_or_sets_processed_finalization
    hn hNoSlash hS rF hProc hId hAlreadyOrStrict

theorem onBlock_finality_update_acceptance_property {f : ℕ} :
    OnBlockFinalityUpdateAcceptanceStatement n f := by
  intro hn hNoSlash S S' B σB hS hFresh hstep hAcc hId hStrict
  exact onBlock_accepts_state_finalization
    hn hNoSlash hS hFresh hstep hAcc hId hStrict

theorem onBlock_finality_update_descends_property {f : ℕ} :
    OnBlockFinalityUpdateDescendsStatement n f := by
  intro hn hNoSlash S S' B σB hS hFresh hstep hAcc hId hAlreadyOrStrict
  exact onBlock_descends_or_accepts_state_finalization
    hn hNoSlash hS hFresh hstep hAcc hId hAlreadyOrStrict

theorem lockIn_property {f : ℕ} :
    LockInStatement n f := by
  intro hn hNoSlash S T hS hFuture F B h_f rF hProc hId hB
  exact lockin_of_processed hn hNoSlash hS hFuture rF hProc hId hB

/-! ## Proved Extensional Order-Independence Surface -/

theorem orderEquivalent_getConfirmed_property :
    OrderEquivalentGetConfirmedStatement n := by
  intro S T B hEq
  exact orderindep_getConfirmed hEq

theorem orderEquivalent_viableTree_property :
    OrderEquivalentViableTreeStatement n := by
  intro S T B hEq
  exact orderindep_viableTree hEq

end Store

end DecoupledConsensus
