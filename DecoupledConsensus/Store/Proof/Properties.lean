import DecoupledConsensus.Store.Statements
import DecoupledConsensus.Store.Proof.Replay

namespace DecoupledConsensus

/-! # Store Property Proof Facade

This module proves the statement definitions from `Store.Statements` by
delegating to the proof modules. It is intentionally thin: theorem statements
stay readable in `Store.Statements`, while proof scripts remain under
`Store.Proof`.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-! ## Unconditional Store Properties -/

theorem proof_hj_monotone_property : HjMonotoneStatement n := by
  intro S T hFuture
  exact future_hj_mono hFuture

theorem proof_key_monotone_property : KeyMonotoneStatement n := by
  intro S T hFuture
  exact future_key_mono hFuture

theorem proof_finality_irreversibility_property :
    FinalityIrreversibilityStatement n := by
  intro S T hFuture
  exact future_F_ancestor hFuture

theorem proof_f_ancestor_j_property : FAncestorJStatement n := by
  intro S hS
  exact reachable_F_ancestor_J hS

theorem proof_f_viable_property : FViableStatement n := by
  intro S hS
  exact reachable_F_viableBool hS

theorem proof_getConfirmed_total_property : GetConfirmedTotalStatement n := by
  intro S hS
  exact ⟨reachable_getConfirmed_nonempty hS, fun hB => getConfirmed_candidate hB⟩

theorem proof_forkChoice_consistency_property :
    ForkChoiceConsistencyStatement n := by
  intro S T B hS hFuture hB
  exact future_getConfirmed_descends_from_F hS hFuture hB

theorem proof_noHigh_justifications_property :
    NoHighJustificationsStatement n := by
  intro S hS
  exact reachable_noHighJustifications hS

/-! ## Accountable Store Properties -/

theorem proof_certChain_property {f : ℕ} :
    CertChainStatement n f := by
  intro hn hNoSlash S F C h_f h hFinal hProc hle
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  let rJ : JustificationRecord S C h := ProcessedJustification.toRecord hProc
  exact certchain_record_compatible hn hNoSlash rF rJ hId hle

theorem proof_certChain_strict_property {f : ℕ} :
    CertChainStrictStatement n f := by
  intro hn hNoSlash S F C h_f h hFinal hProc hpos hlt
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  let rJ : JustificationRecord S C h := ProcessedJustification.toRecord hProc
  exact certchain_record_strict_of_positive
    hn hNoSlash rF rJ hId hpos hlt

theorem proof_upgrade_property {f : ℕ} :
    UpgradeStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f hFinal hProc
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact upgrade_of_processed hn hNoSlash hS hFuture rF hProc hId

theorem proof_finalized_viable_property {f : ℕ} :
    FinalizedViableStatement n f := by
  intro hn hNoSlash S T hS hFuture F h_f hFinal hProc
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact future_finalized_viableBool_of_processedJustification
    hn hNoSlash hS hFuture hId rF.chain rF.final_state
    rF.certificate hProc

theorem proof_finality_update_acceptance_property {f : ℕ} :
    FinalityUpdateAcceptanceStatement n f := by
  intro hn hNoSlash S hS F' h_f hFinal hProc hStrict
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact updateFinalized_accepts_processed_finalization
    hn hNoSlash hS rF hProc hId hStrict

theorem proof_finality_update_descends_property {f : ℕ} :
    FinalityUpdateDescendsStatement n f := by
  intro hn hNoSlash S hS F' h_f hFinal hProc hAlreadyOrStrict
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact updateFinalized_descends_or_sets_processed_finalization
    hn hNoSlash hS rF hProc hId hAlreadyOrStrict

theorem proof_onBlock_finality_update_acceptance_property {f : ℕ} :
    OnBlockFinalityUpdateAcceptanceStatement n f := by
  intro hn hNoSlash S S' B σB hS hFresh hstep hAcc hId hStrict
  exact onBlock_accepts_state_finalization
    hn hNoSlash hS hFresh hstep hAcc hId hStrict

theorem proof_onBlock_finality_update_descends_property {f : ℕ} :
    OnBlockFinalityUpdateDescendsStatement n f := by
  intro hn hNoSlash S S' B σB hS hFresh hstep hAcc hId hAlreadyOrStrict
  exact onBlock_descends_or_accepts_state_finalization
    hn hNoSlash hS hFresh hstep hAcc hId hAlreadyOrStrict

theorem proof_lockIn_property {f : ℕ} :
    LockInStatement n f := by
  intro hn hNoSlash S T hS hFuture F B h_f hFinal hProc hB
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact lockin_of_processed hn hNoSlash hS hFuture rF hProc hId hB

/-! ## Live Store-Output Invariance -/

theorem proof_liveEquivalent_getConfirmed_property :
    LiveEquivalentGetConfirmedStatement n := by
  intro S T B hS hT hEq
  exact liveEquivalent_getConfirmed hS hT hEq

theorem proof_liveComplete_getConfirmed_property :
    LiveCompleteGetConfirmedStatement n := by
  intro input summary S T B hS hT
  exact liveComplete_getConfirmed hS hT

theorem proof_parentFirstReplay_liveComplete_property {f : ℕ} :
    ParentFirstReplayLiveCompleteStatement n f := by
  intro hn hNoSlash input summary S hReplay hPF hNoDup hNoGenesis hInputId
    hSummary
  exact parentFirstReplay_liveComplete hn hNoSlash hReplay hPF hNoDup
    hNoGenesis hInputId hSummary

theorem proof_parentFirstReplay_liveEquivalent_property {f : ℕ} :
    ParentFirstReplayLiveEquivalentStatement n f := by
  intro hn hNoSlash input₁ input₂ S T hReplayS hReplayT hPFS hPFT
    hNoDupS hNoDupT hNoGenesisS hNoGenesisT hInputIdS hInputBlockEq
  exact parentFirstReplay_liveEquivalent_order_independent hn hNoSlash
    hReplayS hReplayT hPFS hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT
    hInputIdS hInputBlockEq

theorem proof_parentFirstReplay_getConfirmed_property {f : ℕ} :
    ParentFirstReplayGetConfirmedStatement n f := by
  intro hn hNoSlash input₁ input₂ S T B hReplayS hReplayT hPFS
    hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT hInputIdS hInputBlockEq
  exact parentFirstReplay_getConfirmed_order_independent hn hNoSlash
    hReplayS hReplayT hPFS hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT
    hInputIdS hInputBlockEq

end Store

end DecoupledConsensus
