module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section
/-!
# SG-target G1 concentration

Claim 3 has one local input and two run-level consequences. A `G1` block has
threshold direct support. The fault bound then supplies an honest contributor
whose preceding-round Section 7 SG target extends the block. Claim 1 is kept
abstract as `SGTargetConeCanonicality`: each such honest target has a cone of
honest Goldfish votes at the chosen interior slot.

The first consequence transfers that target cone to every live `G1` block. The
second uses Claim 2's same-slot common-head theorem to make any two such `G1`
blocks compatible. No recovery-height or nonfinality premise occurs here.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


-- the compatibility layer
-- SGTargetG1ConcentrationRunRetired.lean.

/-- The abstract Claim-1 interface used by Claim 3.

The target is the exact Section 7 SG target emitted by an honest validator in
round `r`. The caller supplies the slot and its second-or-later timing facts;
this interface deliberately does not import Claim 1's in-progress theorem. -/
def SGTargetConeCanonicality (S : Setup V) (rho : Run V)
    (r : Round) (s : Slot) : Prop :=
  ∀ v ∈ rho.honest,
    NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (actionSGBlockAt S rho v r) X)


/-- Claim 1 at one opening boundary, strengthened by the exact fixed-frontier
root lock needed by Claim 4. The height qualification excludes lower cone
targets such as genesis. -/
structure SGTargetOpeningConeRootLock
    (S : Setup V) (rho : Run V) (K : Height) (r : Round) (s : Slot) : Prop where
  canonical : SGTargetConeCanonicality S rho r s
  coneRootLock : ∀ {B : NamedBlock V},
    RunBlock S rho B →
    K ≤ (Protocol.derive_named S.E S.cfg B).h →
    NamedHonestVotesCone S rho s (fun X => Block.Preceq B.erase X) →
    ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG)
        B.erase


/-- A live grade-one block at round `r + 1` is below an honest round-`r` Section
7 SG target.

This is the grade-support witness bridge. Its timing assumptions are exactly
those needed to identify the contributor's projected batch vote with the
honest action target. -/
theorem exists_honestSGTarget_extending_g1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round}
    {w : V} (hw : w ∈ rho.honest)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    {B : Block V}
    (hG1 : Protocol.G1 S.E (gradeViewAt S rho w (r + 1))
      S.hc (r + 1) B = true) :
    ∃ v ∈ rho.honest, Block.Preceq B (actionSGBlockAt S rho v r) :=
  G1_preceq_honestPreviousActionCarrier S adm hfb hw r hpost hcut hG1

/-- Claim 1 transfers from the honest SG target that supports a live `G1` block
to the block itself. -/
theorem honestVotesCone_of_g1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} {s : Slot}
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hcanonical : SGTargetConeCanonicality S rho r s)
    {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hG1 : Protocol.G1 S.E (gradeViewAt S rho w (r + 1))
      S.hc (r + 1) B = true) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq B X) := by
  obtain ⟨v, hv, hBT⟩ := exists_honestSGTarget_extending_g1
    S adm hfb hw hpost hcut hG1
  have htarget : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (actionSGBlockAt S rho v r) X) :=
    hcanonical v hv
  intro x hx hcommittee
  obtain ⟨X, hTX, hXrun, hemit⟩ := htarget x hx hcommittee
  exact ⟨X, Block.preceq_trans hBT hTX, hXrun, hemit⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
