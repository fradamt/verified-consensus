module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Liveness
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches e: the two public finality adapters (design §5 D3)
Both public finality contracts, `FinalizedChainGrowth` and
`HonestProposalFinalization`, share one startup boundary and one pair of
round deadlines from a single common recovery producer. Rather than wait for
that producer (the corresponding branch), these are pre-built over its exact pinned
statement `FinalityAfterGSTPin`, taken here as a hypothesis. Once w4-d2 lands
the producer, each adapter closes by a one-line consumer. The pin uses the
same concrete startup and deadline formulas as the public statements. -/



namespace DecoupledConsensusModel
namespace Proofs
open Internal Execution Statements
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The exact D3 pin (report §5 D3, the corresponding branch), verbatim from earlier
`LivenessContractsRun.lean:86-94`'s private `finality_afterGST`. -/
def FinalityAfterGSTPin (S : Setup V) : Prop :=
  ∀ {extra : Nat}, TimeoutDelayBound S extra → ∀ gap : Round,
    ∀ rho rGST, StrongFinalityRun S rho gap → S.E.t_GST ≤ S.a rGST →
      healingBoundaryTime S
          (rGST + Statements.Instantiation.finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q, rGST ≤ q ∧
        q ≤ rGST + Statements.Instantiation.finalityStartup S gap extra ∧
        RecurringFinalityFrom S rho q (Statements.Instantiation.finalityDeadline S gap extra) ∧
        HonestProposalFinalityFrom S rho q (Statements.Instantiation.finalityDeadline S gap extra)

/-- Finalized-chain growth, retaining the current startup at GST zero. -/
theorem finalizedChainGrowth_of_pins (S : Setup V)
    (finality_afterGST : FinalityAfterGSTPin S) : FinalizedChainGrowth S := by
  constructor
  · intro extra hdelay gap
    intro rho h hgst hhor
    have hpost : S.E.t_GST ≤ S.a 0 := hgst ▸ Proofs.HealingLemmas.a_nonneg S 0
    obtain ⟨q, _, hhi, hrec, _⟩ :=
      finality_afterGST hdelay gap rho 0 h hpost (by simpa using hhor)
    exact ⟨q, by simpa using hhi, hrec⟩
  · intro extra hdelay gap
    intro rho rGST h hpost hhor
    obtain ⟨q, hlo, hhi, hrec, _⟩ :=
      finality_afterGST hdelay gap rho rGST h hpost hhor
    exact ⟨q, hlo, hhi, hrec⟩

/-- Honest-proposal finalization, retaining the current startup exclusion. -/
theorem honestProposalFinalization_of_pins (S : Setup V)
    (finality_afterGST : FinalityAfterGSTPin S) : HonestProposalFinalization S := by
  constructor
  · intro extra hdelay gap
    intro rho h hgst hhor
    have hpost : S.E.t_GST ≤ S.a 0 := hgst ▸ Proofs.HealingLemmas.a_nonneg S 0
    obtain ⟨q, _, hhi, _, hprop⟩ :=
      finality_afterGST hdelay gap rho 0 h hpost (by simpa using hhor)
    exact ⟨q, by simpa using hhi, hprop⟩
  · intro extra hdelay gap
    intro rho rGST h hpost hhor
    obtain ⟨q, hlo, hhi, _, hprop⟩ :=
      finality_afterGST hdelay gap rho rGST h hpost hhor
    exact ⟨q, hlo, hhi, hprop⟩

end Proofs
end DecoupledConsensusModel

end
