import DecoupledConsensus.Store.TheoremStatements
import DecoupledConsensus.Store.Proof.Replay

namespace DecoupledConsensus

/-! # Store Proven-Theorem Proof Facade

This module proves the public theorem-statement definitions from
`Store.TheoremStatements` by delegating to the proof modules. It is
intentionally thin: theorem statements stay readable in
`Store.TheoremStatements`, while proof scripts and proof-internal lemma
surfaces remain under `Store.Proof`.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-! ## Public Store Theorems -/

theorem proof_finality_irreversibility_theorem :
    FinalityIrreversibilityStatement n := by
  intro S T hFuture
  exact future_F_ancestor hFuture

theorem proof_f_ancestor_j_theorem : FAncestorJStatement n := by
  intro S hS
  exact reachable_F_ancestor_J hS

theorem proof_getConfirmed_total_theorem : GetConfirmedTotalStatement n := by
  intro S hS
  exact ⟨reachable_getConfirmed_nonempty hS, fun hB => getConfirmed_candidate hB⟩

theorem proof_forkChoice_consistency_theorem :
    ForkChoiceConsistencyStatement n := by
  intro S T B hS hFuture hB
  exact future_getConfirmed_descends_from_F hS hFuture hB

theorem proof_local_finality_update_theorem {f : ℕ} :
    LocalFinalityUpdateStatement n f := by
  intro hn hNoSlash S S' B σB hS hFresh hstep hAcc hId
  exact onBlock_descends_state_finalization
    hn hNoSlash hS hFresh hstep hAcc hId

theorem proof_lockIn_theorem {f : ℕ} :
    LockInStatement n f := by
  intro hn hNoSlash S T hS hFuture F B h_f hFinal hProc hB
  obtain ⟨rF, hId⟩ := hFinal.exists_record
  exact lockin_of_processed hn hNoSlash hS hFuture rF hProc hId hB

theorem proof_parentFirstReplay_liveEquivalent_theorem {f : ℕ} :
    ParentFirstReplayLiveEquivalentStatement n f := by
  intro hn hNoSlash input₁ input₂ S T hReplayS hReplayT hPFS hPFT
    hNoDupS hNoDupT hNoGenesisS hNoGenesisT hInputIdS hInputBlockEq
  exact parentFirstReplay_liveEquivalent_order_independent hn hNoSlash
    hReplayS hReplayT hPFS hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT
    hInputIdS hInputBlockEq

theorem proof_parentFirstReplay_getConfirmed_theorem {f : ℕ} :
    ParentFirstReplayGetConfirmedStatement n f := by
  intro hn hNoSlash input₁ input₂ S T B hReplayS hReplayT hPFS
    hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT hInputIdS hInputBlockEq
  exact parentFirstReplay_getConfirmed_order_independent hn hNoSlash
    hReplayS hReplayT hPFS hPFT hNoDupS hNoDupT hNoGenesisS hNoGenesisT
    hInputIdS hInputBlockEq

end Store

end DecoupledConsensus
