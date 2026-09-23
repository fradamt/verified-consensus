module
public import DecoupledConsensusStatements.Generic.Conditions

@[expose] public section

/-!
# Generic regimes

Purpose: bundle the atomic conditions into the named regimes used by the
generic result claims.
An auditor checks that each regime exposes its exact premises and that no
proof theorem is hidden in a regime constructor.

Defines: `AgreesUntil`, `Continues`, `BFTRegime`, `RecoveryRegime`,
`RecoveredBy`, `AccountableRegime`, `SleepyRegime`, `LiveSleepyRegime`,
`StrongLiveSleepyRegime`, `FinalityRegime`, and `OutageRegime`.
Read after: `Conditions`.
Read next: `Claims`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

variable {V : Type} {P : DecoupledConsensusModel.Generic.ProtocolSpec V}
  [DecidableEq V] [_root_.Fintype V]

/-- A continuation preserves retained honest validators' event prefixes. -/
structure AgreesUntil
    (rho rho' : DecoupledConsensusModel.Generic.Run V P.Object)
    (cutoff : Time) : Prop where
  honest_subset : rho'.honest ⊆ rho.honest
  events : ∀ v ∈ rho'.honest,
    rho'.events.filter (fun e => decide (e.node = v ∧ e.time < cutoff)) =
      rho.events.filter (fun e => decide (e.node = v ∧ e.time < cutoff))

/-- A continuation agrees before `cut` and reaches `upto`. The event comparison
uses the half-open prefix `time < cut`. -/
structure Continues
    (source rho : DecoupledConsensusModel.Generic.Run V P.Object)
    (cut upto : Time) : Prop where
  agrees : AgreesUntil source rho cut
  covered : upto ≤ rho.horizon

/-- Execution and partial synchrony with a below-one-third, fully awake electorate. -/
structure BFTRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) : Prop where
  execution : ExecutionValid P E I rho
  partialSynchrony : PartialSynchrony P E rho
  gst : E.t_GST ≤ t₀
  committees : HonestCommittees I rho.honest
  belowThird : BelowOneThird E rho.honest
  allAwake : FullParticipation E rho

/-- A bounded recovery prefix with proposer recurrence and a protocol-specific
horizon. -/
structure RecoveryRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time)
    (gap : Nat) : Prop
    extends BFTRegime P E I rho t₀ where
  recurrence : MultiProposerRecurrence I C rho gap
  horizon : rho.horizon = C.prefixEnd t₀ gap

/-- The run is recovered at genesis or after a bounded recovery prefix. -/
inductive RecoveredBy
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Time → Prop
  | genesis : RecoveredBy P E I C rho 0
  | recovered {source : DecoupledConsensusModel.Generic.Run V P.Object}
      {t₀ : Time} {gap : Nat} :
      RecoveryRegime P E I C source t₀ gap →
      Continues source rho (C.prefixEnd t₀ gap) (C.recoveryEnd t₀ gap) →
      SlashableBound I rho →
      RecoveredBy P E I C rho (C.recoveryEnd t₀ gap)

/-- The accountable regime: a well-formed run without one-third-slashable
evidence. -/
structure AccountableRegime
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop extends
  RunWellFormed E I rho where
  slashableBound : SlashableBound I rho

/-- The sleepy regime from `t₀`: validity, partial synchrony after GST ≤ t₀,
honest committees, a fresh-window majority at every time from `t₀`, and a
sound start (genesis or a completed recovery). -/
structure SleepyRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) : Prop where
  execution : ExecutionValid P E I rho
  partialSynchrony : PartialSynchrony P E rho
  gst : E.t_GST ≤ t₀
  committees : HonestCommittees I rho.honest
  windows : ∀ t, t₀ ≤ t → C.participationLag ≤ t →
    t - C.participationLag ≤ rho.horizon →
    WindowMajority E rho.honest C.participationWindow t
  start : RecoveredBy P E I C rho t₀

/-- A live sleepy regime with tier-1 single-proposer recurrence from `t₀`. -/
structure LiveSleepyRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) (gap : Nat) : Prop
    extends SleepyRegime P E I C rho t₀ where
  recurrence : SingleProposerRecurrence I C rho t₀ gap

/-- A strong live sleepy regime: additionally the two openings before it have
honest proposers. -/
structure StrongLiveSleepyRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) (gap : Nat) : Prop
    extends LiveSleepyRegime P E I C rho t₀ gap where
  strongRecurrence : StrongMultiProposerRecurrence I C rho gap

/-- The finality regime from `t₀`: BFT premises, strong recurrence within
`gap ≤ maxGap − 2` periods, and a run long enough to contain the startup. -/
structure FinalityRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time)
    (gap : Nat) : Prop
    extends BFTRegime P E I rho t₀ where
  recurrence : StrongMultiProposerRecurrence I C rho gap
  gapBound : gap + 2 ≤ C.maxGap
  longEnough : t₀ + C.finalityStartup gap ≤ rho.horizon

/-- The outage regime for a stable read at `T` and the half-open outage window
`[b₀, b₁)`. The interval fields also record the boundary needed for delivery
after the window. -/
structure OutageRegime
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object)
    (T b₀ b₁ : Time) : Prop where
  execution : ExecutionValid P E I rho
  partialSynchrony : PartialSynchrony P E rho
  gst : E.t_GST ≤ b₁
  committees : HonestCommittees I rho.honest
  healthy : HealthyPrefixDelivery P E rho b₀
  interval : 0 ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  boundaryPublic : PublicTime E b₀
  participation : ∀ t, C.participationLag ≤ t →
    t ≤ rho.horizon + C.participationLag →
    FreshMajority E rho.honest C t
  slashableBound : SlashableBound I rho
  window : C.outageStart T ≤ b₀ ∧ b₁ + E.Δ ≤ C.expiry T ∧ b₁ + E.Δ ≤ rho.horizon

end DecoupledConsensusModel.Statements.Generic

end
