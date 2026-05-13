import DecoupledConsensus.State.Proof.Properties

namespace DecoupledConsensus

/-! # State Properties

Proved facade for the Section 2 accountable-safety properties.

The proof-free statement definitions live in `State.Statements`. The theorem
wrappers below intentionally expose only that each statement has a proof; the
proof scripts themselves remain under `State.Proof`.
-/

variable {n : ℕ}

namespace State

theorem main_safety_property {f : ℕ} :
    MainSafetyStatement n f :=
  proof_main_safety_property

theorem finalized_blocks_form_chain_property {f : ℕ} :
    FinalizedBlocksFormChainStatement n f :=
  proof_finalized_blocks_form_chain_property

theorem accountable_safety_property {f : ℕ} :
    AccountableSafetyStatement n f :=
  proof_accountable_safety_property

end State

end DecoupledConsensus
