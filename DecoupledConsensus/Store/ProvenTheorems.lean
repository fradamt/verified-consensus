import DecoupledConsensus.Store.Proof.ProvenTheorems

namespace DecoupledConsensus

/-! # Store Proven Theorems

Proved facade for the Section 3 store theorems.

The proof-free statement definitions live in `Store.TheoremStatements`. The
theorem wrappers below intentionally expose only that each public statement has
a proof; the proof scripts themselves remain under `Store.Proof`.
-/

variable {n : ℕ}

namespace Store

/-! ## Public Store Theorems -/

theorem finality_irreversibility_theorem :
    FinalityIrreversibilityStatement n :=
  proof_finality_irreversibility_theorem

theorem f_ancestor_j_theorem : FAncestorJStatement n :=
  proof_f_ancestor_j_theorem

theorem getConfirmed_total_theorem : GetConfirmedTotalStatement n :=
  proof_getConfirmed_total_theorem

theorem forkChoice_consistency_theorem :
    ForkChoiceConsistencyStatement n :=
  proof_forkChoice_consistency_theorem

theorem local_finality_update_theorem {f : ℕ} :
    LocalFinalityUpdateStatement n f :=
  proof_local_finality_update_theorem

theorem lockIn_theorem {f : ℕ} :
    LockInStatement n f :=
  proof_lockIn_theorem

theorem parentFirstReplay_liveEquivalent_theorem {f : ℕ} :
    ParentFirstReplayLiveEquivalentStatement n f :=
  proof_parentFirstReplay_liveEquivalent_theorem

theorem parentFirstReplay_getConfirmed_theorem {f : ℕ} :
    ParentFirstReplayGetConfirmedStatement n f :=
  proof_parentFirstReplay_getConfirmed_theorem

end Store

end DecoupledConsensus
