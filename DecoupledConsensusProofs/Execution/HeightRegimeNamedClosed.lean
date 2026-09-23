module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.RecoveryInitialSourceNamedActionHistory
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGSelectorPrefixSeedNamedClosed

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The run-scoped twin of `NamedOldTargetRootBelow`.

This is the same statement as `NamedOldTargetRootBelow`, with the additional
premise `RunBlock S rho R` on the named old root. The premise is required to
use the run-scoped root-collision contract when an erased witness equality
must be lifted back to named blocks. -/
def NamedOldTargetRootBelowRun
    (S : Setup V) (rho : Run V) (first : Nat) (blocked : Height)
    (T : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    strictEventIndex rho (S.a a.round) < first →
    ∀ R : NamedBlock V, RunBlock S rho R →
      (Protocol.derive_named S.E S.cfg R).h = blocked →
      a.height_pair.erase = HeightPair.target blocked R.erase.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R.erase →
      ∀ w ∈ rho.honest, ∀ time : Time,
        blocked < (rho.storeBeforeTime S w time).h_max →
        Protocol.get_fg_root
          (rho.storeBeforeTime S w time).core.toHealing.toFG = R.erase →
        NamedBlock.Preceq R T





/-- Closed additive restatement of the named base constructor. -/
theorem NamedHeightRegimeBase.exists_regime_closed
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBase S rho r0 blocked first Tprev) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho r0 blocked first i a ta
        Cfg T Tprev a.round := by
  apply h.exists_regime adm hbelow hgst
  intro i a ta hframe hiStart hiStop haHon hiEvent hiOutput hrow hfrontier
  exact honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrame
    S adm hbelow hgst hframe hiStart hiStop haHon hiEvent hiOutput
      hrow hfrontier

#print axioms NamedHeightRegimeBase.exists_regime_closed

/-- The original named old-root contract weakens to its run-scoped twin. -/
theorem NamedOldTargetRootBelow.toRun
    {S : Setup V} {rho : Run V} {first : Nat} {blocked : Height}
    {T : NamedBlock V}
    (h : NamedOldTargetRootBelow S rho first blocked T) :
    NamedOldTargetRootBelowRun S rho first blocked T := by
  intro a ta ha hemit hbefore R _hRrun hRh hpair hR w hw time
    hfrontier hroot
  exact h a ta ha hemit hbefore R hRh hpair hR w hw time
    hfrontier hroot

theorem NamedHeightRegime.oldRootRun
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (h : NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0) :
    NamedOldTargetRootBelowRun S rho first blocked T :=
  h.pred.toRun





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
