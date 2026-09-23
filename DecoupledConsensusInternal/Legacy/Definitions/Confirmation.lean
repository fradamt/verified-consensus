module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ConfirmationScore
public import DecoupledConsensusInternal.Legacy.Definitions.NamedConfirmationWalk
public import DecoupledConsensusStatements.Instantiation.RoundTimes
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! Definitions used by the final review statements. No proof obligations are assumed here. -/

namespace DecoupledConsensusModel
namespace Internal

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The largest `h_max` held by an honest store immediately before event
index `n`. The value is zero if the honest set is empty. -/
noncomputable def honestHMaxBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) : Height :=
  rho.honest.sup fun v => (rho.stateBefore S n v).st.h_max

/-- Confirmation safety from `t₀` on: any two honest nodes' recorded
confirmations, at any two times in `[t₀, horizon]`, are compatible
(PROTOCOL.md#the-complete-protocol). -/
def ConfirmationCompatibleFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ∀ u ∈ ρ.honest, ∀ v ∈ ρ.honest, ∀ t t' : Time, t₀ ≤ t → t₀ ≤ t' →
    t ≤ ρ.horizon → t' ≤ ρ.horizon →
    Block.compatible (ρ.storeAt S u t).latest_confirmed
      (ρ.storeAt S v t').latest_confirmed = true

/-- Each honest node's recorded confirmation is nondecreasing along `⪯` from `t₀`
on — the monotonicity `Σ.latest_confirmed`'s own guard supplies
(PROTOCOL.md#the-complete-protocol). -/
def ConfirmationMonotoneFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ∀ v ∈ ρ.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ ρ.horizon →
    Block.Preceq (ρ.storeAt S v t).latest_confirmed (ρ.storeAt S v t').latest_confirmed

/-- Confirmation liveness from `t₀`: every positive in-horizon confirmation
evaluation by every honest validator is genuine. -/
def ConfirmationRenewalFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ∀ s : Slot, 0 < s → t₀ ≤ Protocol.confirmation_time S.E s →
    Protocol.confirmation_time S.E s ≤ ρ.horizon →
      ∀ v ∈ ρ.honest, GenuineConfirmationAt S ρ v s

/-- Confirmation liveness for the slots at or after `t₀`: an honest slot-`s`
proposer emits a slot-`s` block at `t_s`, that block is every honest node's
`live_confirmed` at `t_s + 6Δ` **exactly**, and from that evaluation on every
honest node's exposed `latest_confirmed` descends from it (rev. 3 §8, (ii)).

The two fields have different roles in the integrated §7 protocol.
`live_confirmed` is the current walk result and can fall back to a shallower FG
root. `latest_confirmed` records user confirmation progress. It is monotone
in a proved safe regime and can replace a conflicting record during healing. -/
def ProposalConfirmedFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ∀ s : Slot, 0 < s → t₀ ≤ Protocol.proposal_time S.E s →
    S.E.proposer s ∈ ρ.honest →
    Protocol.confirmation_time S.E s ≤ ρ.horizon →
    ∃ B : NamedBlock V, B.slot = s ∧
      ρ.emits S (S.E.proposer s) (Object.block B) (Protocol.proposal_time S.E s) ∧
      (∀ v ∈ ρ.honest,
        (ρ.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = B.erase) ∧
      (∀ v ∈ ρ.honest, ∀ t : Time, Protocol.confirmation_time S.E s ≤ t →
        t ≤ ρ.horizon → Block.Preceq B.erase (ρ.storeAt S v t).latest_confirmed)

/-- The available chain from `t₀`: safety, monotonicity and liveness together.
P3(a), P3(b) and P4's (C1) are this predicate at three different `t₀`. -/
def AvailableChainFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ConfirmationCompatibleFrom S ρ t₀ ∧ ConfirmationMonotoneFrom S ρ t₀ ∧
    ProposalConfirmedFrom S ρ t₀

/-- The confirmation-centered available-chain surface: safety, stable-record
monotonicity, and genuine-confirmation renewal. Unlike `AvailableChainFrom`, its
liveness clause does not identify the result with the same-slot proposal. -/
def AvailableConfirmationsFrom (S : Setup V) (ρ : Run V) (t₀ : Time) : Prop :=
  ConfirmationCompatibleFrom S ρ t₀ ∧ ConfirmationMonotoneFrom S ρ t₀ ∧
    ConfirmationRenewalFrom S ρ t₀

end Internal
end DecoupledConsensusModel

end
