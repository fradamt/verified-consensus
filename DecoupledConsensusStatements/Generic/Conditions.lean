module
public import DecoupledConsensusModel.Generic.Env
public import DecoupledConsensusStatements.Generic.Constants
public import DecoupledConsensusStatements.Generic.Properties

@[expose] public section

/-!
# Generic atomic conditions

Purpose: define the atomic well-formedness, network, participation, committee,
and proposer premises for the generic claims.
An auditor checks each premise independently and verifies that this file does
not hide a regime bundle or a proof theorem.

Defines: execution conditions, synchrony and participation predicates,
committee conditions, and proposer recurrence conditions.
Read after: `Properties`.
Read next: `Regimes`, then `Claims`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

variable {V : Type} {P : DecoupledConsensusModel.Generic.ProtocolSpec V}
  [DecidableEq V] [_root_.Fintype V]

/-- A public time is an integer multiple of the environment's time unit. -/
def PublicTime (E : DecoupledConsensusModel.Generic.Env V) (t : Time) : Prop :=
  ∃ k : Nat, t = (k : Time) * E.Δ

/-- The event schedule is sorted, finite, honest-only, and total on public times. -/
structure ScheduleWellFormed
    (E : DecoupledConsensusModel.Generic.Env V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_public : ∀ v t,
    DecoupledConsensusModel.Generic.Event.tick v t ∈ rho.events → PublicTime E t
  tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime E t → 0 ≤ t → t ≤ rho.horizon →
    DecoupledConsensusModel.Generic.Event.tick v t ∈ rho.events

/-- Delivered objects satisfy the wire, dependency, and freshness checks. -/
structure DeliveryWellFormed
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  wire : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (DecoupledConsensusModel.Generic.Event.deliver v o t) →
      P.wellFormed o = true
  deps : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (DecoupledConsensusModel.Generic.Event.deliver v o t) →
      P.depsPresent (DecoupledConsensusModel.Generic.Run.stateBefore P rho i v) o = true
  fresh : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (DecoupledConsensusModel.Generic.Event.deliver v o t) →
      P.processed (DecoupledConsensusModel.Generic.Run.stateBefore P rho i v) o = false

/-- Signatures are unforgeable: an object attributed to an honest validator —
processed directly or carried by a processed object — was emitted by that
validator. -/
structure UnforgeableSignatures
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  unforgeable : ∀ v o t,
    DecoupledConsensusModel.Generic.Run.processes P rho v o t →
      ∀ u ∈ rho.honest, P.author o = some u →
        ∃ t', t' ≤ t ∧ DecoupledConsensusModel.Generic.Run.emits P rho u o t'
  carried : ∀ v o t,
    DecoupledConsensusModel.Generic.Run.processes P rho v o t →
      ∀ o', P.carries o o' → ∀ u ∈ rho.honest, P.author o' = some u →
        ∃ t', t' ≤ t ∧ DecoupledConsensusModel.Generic.Run.emits P rho u o' t'

/-- A run with sorted events, honest-only events, a nonnegative horizon, and
unforgeable signatures. -/
structure UnforgeableRun
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop extends
  UnforgeableSignatures P rho where
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  horizon_nonneg : 0 ≤ rho.horizon

/-- The non-network execution premises and the interface idealization. -/
structure ExecutionValid
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop extends
  ScheduleWellFormed E rho, DeliveryWellFormed P rho, UnforgeableSignatures P rho where
  idealization : I.idealization rho

/-- A sorted run with a nonnegative horizon and the interface's idealization;
reads are taken at times in `[0, horizon]`. -/
structure RunWellFormed
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  idealization : I.idealization rho

/-- No evidence occurs between two certificates assembled from the run. -/
def SlashableBound (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop :=
  ∀ c c', I.inRun rho c → I.inRun rho c' → ¬ I.evidence c c'

/-- Broadcast and accepted-object relay complete within the post-GST bound, except for objects the receiver's state at the deadline excludes (a block that conflicts with the receiver's finalized block). -/
structure PartialSynchrony
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    DecoupledConsensusModel.Generic.Run.emits P rho v o t → ∀ w ∈ rho.honest,
      max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes
            (DecoupledConsensusModel.Generic.Run.stateBeforeTime P rho
              (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
          ∃ j, DecoupledConsensusModel.Generic.Run.handlesAt P rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    DecoupledConsensusModel.Generic.Run.acceptsAt P rho i v o t → ∀ w ∈ rho.honest,
      P.processed
          (DecoupledConsensusModel.Generic.Run.stateBefore P rho (i + 1) w) o = false →
        max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes
            (DecoupledConsensusModel.Generic.Run.stateBeforeTime P rho
              (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
            ∃ j, DecoupledConsensusModel.Generic.Run.handlesAt P rho j w o t'

/-- The same broadcast and relay guarantees on a finite healthy prefix, with the same exclusion. -/
structure HealthyPrefixDelivery
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    DecoupledConsensusModel.Generic.Run.emits P rho v o t → ∀ w ∈ rho.honest,
      t + E.Δ ≤ cut →
        P.excludes
            (DecoupledConsensusModel.Generic.Run.stateBeforeTime P rho
              (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
          ∃ j, DecoupledConsensusModel.Generic.Run.handlesAt P rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    DecoupledConsensusModel.Generic.Run.acceptsAt P rho i v o t → ∀ w ∈ rho.honest,
      P.processed
          (DecoupledConsensusModel.Generic.Run.stateBefore P rho (i + 1) w) o = false →
        t + E.Δ ≤ cut →
        P.excludes
            (DecoupledConsensusModel.Generic.Run.stateBeforeTime P rho
              (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
            ∃ j, DecoupledConsensusModel.Generic.Run.handlesAt P rho j w o t'

/-- Honest validators awake at the specified time. -/
def awakeAt (E : DecoupledConsensusModel.Generic.Env V) (H : Finset V)
    (t : Time) : Finset V :=
  H.filter (fun v => E.awake v t = true)

/-- Honest validators awake at some time in the half-open interval `[a, b)`. -/
noncomputable def awakeIn (E : DecoupledConsensusModel.Generic.Env V) (H : Finset V)
    (a b : Time) : Finset V := by
  classical
  exact H.filter (fun v => ∃ u, a ≤ u ∧ u < b ∧ E.awake v u = true)

/-- Honest awake weight in a window exceeds faulty weight. -/
def WindowMajority (E : DecoupledConsensusModel.Generic.Env V) (H : Finset V)
    (w : Time) (t : Time) : Prop :=
  E.electorate.weightOf (Finset.univ \ H) <
    E.electorate.weightOf (awakeIn E H (t - w) t)

/-- Every honest validator is awake at every time from GST to the run horizon. -/
def FullParticipation (E : DecoupledConsensusModel.Generic.Env V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true

/-- Faulty validators hold less than one third of the total weight. -/
def BelowOneThird (E : DecoupledConsensusModel.Generic.Env V) (H : Finset V) : Prop :=
  3 * E.electorate.weightOf (Finset.univ \ H) < E.electorate.totalWeight

/-- Fresh majority (outage participation, time form): the honest weight awake
at `t − lag` (the fresh validators) outweighs the faulty weight plus the stale
honest weight, i.e. honest validators awake somewhere in `[t − window,
t − lag)` but not at `t − lag`. -/
def FreshMajority (E : DecoupledConsensusModel.Generic.Env V) (H : Finset V)
    (C : Constants) (t : Time) : Prop :=
  E.electorate.weightOf
      ((Finset.univ \ H) ∪
        (awakeIn E H (t - C.participationWindow) (t - C.participationLag) \
          awakeAt E H (t - C.participationLag))) <
    E.electorate.weightOf (awakeAt E H (t - C.participationLag))

/-- Every slot committee has a strict honest majority by count. -/
def HonestCommittees (I : Interface P) (H : Finset V) : Prop :=
  ∀ s : Slot, (I.committee s).card < 2 * ((I.committee s) ∩ H).card

/-- The opening slot `s` and the following `proposerSlots − 1` slots all have
honest proposers. -/
def MultiProposerAt (I : Interface P) (C : Constants) (H : Finset V) (s : Slot) : Prop :=
  I.opening s ∧ ∀ k < C.proposerSlots, I.proposer (s + k) ∈ H

/-- Tier 1, single-proposer recurrence: from `t₀`, every trigger time whose `gap`-period
window ends inside the run sees an honest proposal strictly after it and within
the window. Confirmed growth needs nothing more. -/
def SingleProposerRecurrence (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) (gap : Nat) : Prop :=
  ∀ t : Time, t₀ ≤ t → t + gap * C.period ≤ rho.horizon →
    ∃ s, t < I.proposalTime s ∧ I.proposalTime s ≤ t + gap * C.period ∧
      I.proposer s ∈ rho.honest

/-- Tier 2, multi-proposer recurrence: within `gap` periods of every nonnegative
time a multi-proposer window starts: an opening slot and the following
`proposerSlots − 1` slots all have honest proposers; recovery and stable growth use it. -/
def MultiProposerRecurrence (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (gap : Nat) : Prop :=
  ∀ t : Time, 0 ≤ t → ∃ s, t < I.proposalTime s ∧
    I.proposalTime s ≤ t + gap * C.period ∧
    MultiProposerAt I C rho.honest s

/-- Tier 3, strong multi-proposer recurrence: as tier 2, and every opening in the
two periods before that window also has an honest proposer; finality uses it.

In continuous time the smallest satisfiable strong gap is 3 (the window
`[t + 2·period, t + gap·period]` is a point at gap 2), so the finality claims
are non-vacuous only for `gap ≥ 3`, hence `K ≥ 5`; this is one period more than
the paper's round-sampled premise. The finality fixture witnesses gap 3 at
`K = 5`. -/
def StrongMultiProposerRecurrence (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (gap : Nat) : Prop :=
  ∀ t : Time, 0 ≤ t → ∃ s, t + 2 * C.period ≤ I.proposalTime s ∧
    I.proposalTime s ≤ t + gap * C.period ∧
    MultiProposerAt I C rho.honest s ∧
    ∀ s', I.opening s' → I.proposalTime s - 2 * C.period ≤ I.proposalTime s' →
      I.proposalTime s' < I.proposalTime s → I.proposer s' ∈ rho.honest


end DecoupledConsensusModel.Statements.Generic

end
