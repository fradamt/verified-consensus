import DecoupledConsensus.Store.Proof.Properties

namespace DecoupledConsensus

/-! # Store Properties

Proved facade for the Section 3 store properties.

The proof-free statement definitions live in `Store.Statements`. The theorem
wrappers below intentionally expose only that each statement has a proof; the
proof scripts themselves remain under `Store.Proof`.
-/

variable {n : ℕ}

namespace Store

/-! ## Unconditional Store Properties -/

theorem hj_monotone_property : HjMonotoneStatement n :=
  proof_hj_monotone_property

theorem key_monotone_property : KeyMonotoneStatement n :=
  proof_key_monotone_property

theorem finality_irreversibility_property :
    FinalityIrreversibilityStatement n :=
  proof_finality_irreversibility_property

theorem f_ancestor_j_property : FAncestorJStatement n :=
  proof_f_ancestor_j_property

theorem f_viable_property : FViableStatement n :=
  proof_f_viable_property

theorem getConfirmed_total_property : GetConfirmedTotalStatement n :=
  proof_getConfirmed_total_property

theorem forkChoice_consistency_property :
    ForkChoiceConsistencyStatement n :=
  proof_forkChoice_consistency_property

theorem noHigh_justifications_property :
    NoHighJustificationsStatement n :=
  proof_noHigh_justifications_property

/-! ## Accountable Store Properties -/

theorem certChain_property {f : ℕ} :
    CertChainStatement n f :=
  proof_certChain_property

theorem certChain_strict_property {f : ℕ} :
    CertChainStrictStatement n f :=
  proof_certChain_strict_property

theorem upgrade_property {f : ℕ} :
    UpgradeStatement n f :=
  proof_upgrade_property

theorem finalized_viable_property {f : ℕ} :
    FinalizedViableStatement n f :=
  proof_finalized_viable_property

theorem finality_update_acceptance_property {f : ℕ} :
    FinalityUpdateAcceptanceStatement n f :=
  proof_finality_update_acceptance_property

theorem finality_update_descends_property {f : ℕ} :
    FinalityUpdateDescendsStatement n f :=
  proof_finality_update_descends_property

theorem onBlock_finality_update_acceptance_property {f : ℕ} :
    OnBlockFinalityUpdateAcceptanceStatement n f :=
  proof_onBlock_finality_update_acceptance_property

theorem onBlock_finality_update_descends_property {f : ℕ} :
    OnBlockFinalityUpdateDescendsStatement n f :=
  proof_onBlock_finality_update_descends_property

theorem lockIn_property {f : ℕ} :
    LockInStatement n f :=
  proof_lockIn_property

/-! ## Live Store-Output Invariance -/

theorem liveEquivalent_getConfirmed_property :
    LiveEquivalentGetConfirmedStatement n :=
  proof_liveEquivalent_getConfirmed_property

theorem liveComplete_getConfirmed_property :
    LiveCompleteGetConfirmedStatement n :=
  proof_liveComplete_getConfirmed_property

theorem parentFirstReplay_liveComplete_property {f : ℕ} :
    ParentFirstReplayLiveCompleteStatement n f :=
  proof_parentFirstReplay_liveComplete_property

theorem parentFirstReplay_liveEquivalent_property {f : ℕ} :
    ParentFirstReplayLiveEquivalentStatement n f :=
  proof_parentFirstReplay_liveEquivalent_property

theorem parentFirstReplay_getConfirmed_property {f : ℕ} :
    ParentFirstReplayGetConfirmedStatement n f :=
  proof_parentFirstReplay_getConfirmed_property

end Store

end DecoupledConsensus
