module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ProposalSources
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Legacy.Definitions.SafetyRegimes

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! Compatibility import. See `docs/REVIEW_GUIDE.md` for the review boundary. -/

namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Both participation regimes, independently of the open strong-liveness obligation. -/
structure DynamicParticipationSafety (S : Setup V) : Prop where
  finalizedPrefix : ∀ rho, FinalizedPrefixConfirmed S rho
  genesis : ∀ rho, AdmissibleCore S rho →
    -- Explicit and TEMPORARY (addendum 34, option (a)): the confirmation duty's
    -- stable write precedes the record it writes at the same read. A regime
    -- fact, not yet a run invariant. Discharged, and removed, by the
    -- stable-record canonicity theorem; that discharge is mandatory.
    HonestHeadExtendsStableFrom S rho 0 →
    HonestCommittees S rho.honest →
    S.E.t_GST = 0 →
    (∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r) →
    GSTZeroGuarantees S rho
  phaseShift : ∀ rho rGST gap delayExtra n,
    Admissible S rho →
    -- Explicit and TEMPORARY (addendum 34, option (a)): the confirmation duty's
    -- stable write precedes the record it writes at the same read. A regime
    -- fact, not yet a run invariant. Discharged, and removed, by the
    -- stable-record canonicity theorem; that discharge is mandatory.
    HonestHeadExtendsStableFrom S rho 0 →
    HonestCommittees S rho.honest → BelowOneThird S rho.honest →
    MultiProposerRecurrence S rho gap S.E.t_GST → TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
    BoundedPhaseStart S rho rGST gap delayExtra n → rho.horizon = S.a (n + gap) →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧ n + gap ≤ m + gap ∧
      ∃ B : NamedBlock V,
      Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot m) = some B ∧
      ∀ rho', AdmissibleCore S rho' →
        -- Explicit and TEMPORARY (addendum 34, option (a)): as above, for the
        -- continued run. Discharged by stable-record canonicity.
        HonestHeadExtendsStableFrom S rho' 0 →
        HonestCommittees S rho'.honest → SlashableBound S rho' →
        AgreesUntil rho rho' (S.a (n + gap)) → S.a (n + gap) ≤ rho'.horizon →
        (∀ r, n + gap < r → S.a (r - 1) ≤ rho'.horizon →
          AwakeWindowMajority S.E (fun v => (S.node v).awake) rho'.honest S.hc.η_SG r) →
        PhaseShiftSafety S rho' n (S.hc.opening_slot m) B.erase

end Internal
end DecoupledConsensusModel

end
