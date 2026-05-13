import DecoupledConsensus.State.TheoremStatements
import DecoupledConsensus.State.Proof.Safety

namespace DecoupledConsensus

/-! # State Proven-Theorem Proof Facade

This module proves the theorem-statement definitions from
`State.TheoremStatements` by delegating to the proof modules. The public proved
facade is `State.ProvenTheorems`, which references these named proof constants
without showing the proof scripts.
-/

variable {n : ℕ}

open scoped Block

namespace State

theorem proof_main_safety_theorem {f : ℕ} :
    MainSafetyStatement n f := by
  intro hn B₁ B₂ C h_f hId chain₁ hFinal chain₂ hHeight
  rcases hFinal with ⟨hC₁, hF₁, hCert₁⟩
  exact main_safety_between hn hId chain₁ hF₁ hCert₁ chain₂ hHeight

theorem proof_finalized_blocks_form_chain_theorem {f : ℕ} :
    FinalizedBlocksFormChainStatement n f := by
  intro hn B₁ B₂ C C' h_f h_f' hId chain₁ hFinal₁ chain₂ hFinal₂ hLE
  rcases hFinal₁ with ⟨hC₁, hF₁, hCert₁⟩
  rcases hFinal₂ with ⟨hC₂, hF₂, hCert₂⟩
  exact finalized_chain_between hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂ hLE

theorem proof_accountable_safety_theorem {f : ℕ} :
    AccountableSafetyStatement n f := by
  intro hn B₁ B₂ C C' h_f h_f' hId chain₁ hFinal₁ chain₂ hFinal₂
  rcases hFinal₁ with ⟨hC₁, hF₁, hCert₁⟩
  rcases hFinal₂ with ⟨hC₂, hF₂, hCert₂⟩
  exact accountable_safety_between hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂

end State

end DecoupledConsensus
