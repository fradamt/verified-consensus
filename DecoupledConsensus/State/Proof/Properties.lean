import DecoupledConsensus.State.Statements
import DecoupledConsensus.State.Proof.Safety

namespace DecoupledConsensus

/-! # State Property Proof Facade

This module proves the statement definitions from `State.Statements` by
delegating to the proof modules. The public proved facade is
`State.Properties`, which references these named proof constants without
showing the proof scripts.
-/

variable {n : ℕ}

open scoped Block

namespace State

theorem proof_main_safety_property {f : ℕ} :
    MainSafetyStatement n f := by
  intro hn B₁ B₂ C h_f hId hFinal chain₂ hHeight
  rcases hFinal with ⟨chain₁, hC₁, hF₁, hCert₁⟩
  exact main_safety hn hId chain₁ hF₁ hCert₁ chain₂ hHeight

theorem proof_finalized_blocks_form_chain_property {f : ℕ} :
    FinalizedBlocksFormChainStatement n f := by
  intro hn B₁ B₂ C C' h_f h_f' hId hFinal₁ hFinal₂ hLE
  rcases hFinal₁ with ⟨chain₁, hC₁, hF₁, hCert₁⟩
  rcases hFinal₂ with ⟨chain₂, hC₂, hF₂, hCert₂⟩
  exact finalized_chain hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂ hLE

theorem proof_accountable_safety_property {f : ℕ} :
    AccountableSafetyStatement n f := by
  intro hn B₁ B₂ C C' h_f h_f' hId hFinal₁ hFinal₂
  rcases hFinal₁ with ⟨chain₁, hC₁, hF₁, hCert₁⟩
  rcases hFinal₂ with ⟨chain₂, hC₂, hF₂, hCert₂⟩
  exact accountable_safety hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂

end State

end DecoupledConsensus
