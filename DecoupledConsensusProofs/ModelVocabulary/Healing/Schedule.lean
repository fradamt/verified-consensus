module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Objects
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.ChainState
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.Transition
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Store
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.Objects
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.FGForkChoice.Finality
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Protocol.ValidatorClient

@[expose] public section

/-!
# §6.1 Round schedule — `sec:healing-schedule` (PROTOCOL.md `sec:healing-schedule`)

`R ≥ 2`, the four grade cutoffs around the opening slot, and the action time
`a_r = t_{rR} + 6Δ`.

This is where §3's one free parameter is fixed. `Protocol.SGConfig.a` is a bare
`Round → Time` with no stated relation to round `r`'s slots (F3.1, choices S3.3);
§6 sets it to the opening slot's confirmation evaluation and thereby forces
`R ≥ 2` (PROTOCOL.md `sec:healing-schedule`). Rather than restating the SG parameters,
`HealConfig` carries `R ≥ 2` and `η_SG` and *produces* the §3 structure through
`sgConfig`, so the two layers cannot disagree about `R`, `η_SG` or `a_r`.

The cutoffs take `Δ` as an argument rather than an `Env V`: they are validator-free
arithmetic, and `sgConfig` has to be validator-free because `SGConfig` is.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- The weaker bound used by the proof-side round arithmetic. -/
theorem HealConfig.R_ge_two (hc : HealConfig) : 2 ≤ hc.R :=
  le_trans (by decide) hc.R_ge_three

namespace HealConfig

variable (hc : HealConfig)

/-- §6.1 `Γ_r^{−1} = t_{rR} − Δ` (PROTOCOL.md `sec:healing-schedule`): the
earliest grade cutoff, which is the view freeze of the slot before the
opening slot. -/
def Γ_neg1 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) - Δ

/-- §6.1 `Γ_r^0 = t_{rR}` (PROTOCOL.md `sec:healing-schedule`): the opening-slot proposal
instant. -/
def Γ_0 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r)

/-- §6.1 `Γ_r^1 = t_{rR} + Δ` (PROTOCOL.md `sec:healing-schedule`): the opening-slot Goldfish
vote instant, at which `set_fresh_root` runs first. -/
def Γ_1 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + Δ

/-- §6.1 `Γ_r^2 = t_{rR} + 2Δ` (PROTOCOL.md `sec:healing-schedule`): the opening-slot support
cutoff, and the freeze on the veto's blocks (PROTOCOL.md `sec:grades`,
"never becomes a veto"). -/
def Γ_2 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + 2 * Δ

end HealConfig

section Alignment

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §6.1 `Γ_r^0` is the opening slot's proposal instant
(PROTOCOL.md `sec:healing-schedule`). -/
theorem Γ_0_eq_proposal_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.Γ_0 E.Δ r = Protocol.proposal_time E (hc.opening_slot r) := rfl

/-- §6.1 `Γ_r^1` is the opening slot's Goldfish vote instant
(PROTOCOL.md `sec:healing-schedule`). -/
theorem Γ_1_eq_vote_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.Γ_1 E.Δ r = Protocol.vote_time E (hc.opening_slot r) := rfl

/-- §6.1 `a_r` is the opening slot's confirmation evaluation
(PROTOCOL.md `sec:healing-schedule`). This is why `on_tick` recomputes the
confirmation before it runs `attest` in the same tick
(PROTOCOL.md `sec:healing-schedule`, `alg:store`). -/
theorem a_eq_confirmation_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r = Protocol.confirmation_time E (hc.opening_slot r) := rfl

/-- §6.1 `a_r = t_{rR+1} + 2Δ`, so the action fires in the slot **after** the
opening slot; `R ≥ 2` is what keeps that slot inside round `r`
(PROTOCOL.md `sec:goldfish-schedule`, `sec:healing-schedule`, F6.16). -/
theorem a_eq_support_cutoff_succ (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r = Protocol.support_cutoff E (hc.opening_slot r + 1) :=
  Protocol.confirmation_time_eq_support_cutoff_succ E (hc.opening_slot r)

end Alignment

end Protocol
end DecoupledConsensusModel

end
