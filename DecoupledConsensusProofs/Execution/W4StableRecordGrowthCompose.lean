module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Liveness

@[expose] public section

/-!
#  C3 — the stable-record growth composer

The public field `Statements.StableRecordGrowth` is exactly the pair of its two
regime branches (`DecoupledConsensusStatements/Liveness.lean:42-50`). This leaf
composes them. Both branches are taken as `∀`-hypotheses with the exact pinned
statements of the corresponding branch (GST zero) and the corresponding branch (after GST), so the composer
is available before either branch lands; the closing consumer is one line.
-/



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The public stable-record growth field from its two regime branches.

`hgst` is the exact pinned statement of `stableRecordGrowth_gstZero` (branches
w4-c1) and `hafter` the exact pinned statement of `stableRecordGrowth_afterGST`
(the corresponding branch), both as written in the liveness audit's work list §5 C. -/
theorem stableRecordGrowth_of_pins (S : Setup V)
    (hgst : ∀ rho, WeakGenesis S rho →
      ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
        StableRecordGrowthFrom S rho 0 (gap + S.hc.η_SG - 1))
    (hafter : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          ∀ continuationGap,
            ProposerOpeningCarrierRecurrence S rho' continuationGap →
              StableRecordGrowthFrom S rho'
                (S.hc.opening_slot m) (continuationGap + S.hc.η_SG - 1)) :
    StableRecordGrowth S :=
  { gstZero := hgst
    afterGST := hafter }

#print axioms stableRecordGrowth_of_pins

end Proofs
end DecoupledConsensusModel

end
