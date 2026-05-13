import DecoupledConsensus.State.Proof.ProvenTheorems

namespace DecoupledConsensus

/-! # State Proven Theorems

Proved facade for the Section 2 accountable-safety theorems.

The proof-free statement definitions live in `State.TheoremStatements`. The
theorem wrappers below intentionally expose only that each public statement has
a proof; the proof scripts themselves remain under `State.Proof`.
-/

variable {n : ℕ}

namespace State

theorem main_safety_theorem {f : ℕ} :
    MainSafetyStatement n f :=
  proof_main_safety_theorem

theorem finalized_blocks_form_chain_theorem {f : ℕ} :
    FinalizedBlocksFormChainStatement n f :=
  proof_finalized_blocks_form_chain_theorem

theorem accountable_safety_theorem {f : ℕ} :
    AccountableSafetyStatement n f :=
  proof_accountable_safety_theorem

end State

end DecoupledConsensus
