module
public import DecoupledConsensusModel
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Setup
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedEvent
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedReceiptCalls

@[expose] public section

/-! Full named environmental contracts over the concrete run. Schedule and
bounds retain their existing formulas. The named recipient relation
counts actual direct/self/carried calls; it does not promise successful admission.
No compatibility contract or supplied configuration is changed. -/
namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

structure NamedScheduleWellFormed (S : Setup V) (rho : NamedRun V) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_public : ∀ v t, NamedEvent.tick v t ∈ rho.events → PublicTime S t
  tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime S t → 0 ≤ t → t ≤ rho.horizon →
    NamedEvent.tick v t ∈ rho.events

structure NamedDeliveryWellFormed (S : Setup V) (rho : NamedRun V) : Prop where
  wire : ∀ (i : Nat) v o t, rho.events[i]? = some (.deliver v o t) →
    NamedReceipt.wellFormed S o = true
  deps : ∀ (i : Nat) v o t, rho.events[i]? = some (.deliver v o t) →
    NamedReceipt.depsPresent (NamedRun.stateBefore S rho i v).st o = true
  fresh : ∀ (i : Nat) v o t, rho.events[i]? = some (.deliver v o t) →
    NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o = false

structure NamedUnforgeable (S : Setup V) (rho : NamedRun V) : Prop where
  unforgeable : ∀ v o t, NamedRun.processes S rho v o t →
    ∀ u ∈ rho.honest, o.author = some u →
      ∃ t', t' ≤ t ∧ NamedRun.emits S rho u o t'
  carried_gf : ∀ v B t, NamedRun.processes S rho v (.block B) t →
    ∀ u ∈ B.gf_votes, u.val_index ∈ rho.honest →
      ∃ t', t' ≤ t ∧ NamedRun.emits S rho u.val_index (.gfVote u) t'
  carried_attest : ∀ v B t, NamedRun.processes S rho v (.block B) t →
    ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
      ∃ t', t' ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) t'

structure NamedSynchrony (S : Setup V) (rho : NamedRun V) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, NamedRun.emits S rho v o t →
    ∀ w ∈ rho.honest, max t S.E.t_GST + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st o = false →
      ∃ t', t ≤ t' ∧ t' < max t S.E.t_GST + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t'
  relay_block : ∀ v ∈ rho.honest, ∀ (i : Nat) (B : NamedBlock V) (t : Time),
    NamedRun.acceptsAt S rho i v (.block B) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.block B) = false →
      max t S.E.t_GST + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st (.block B) = false →
      ∃ t', t ≤ t' ∧ t' < max t S.E.t_GST + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.block B) t'
  relay_gf_vote : ∀ v ∈ rho.honest, ∀ (i : Nat) (u : GoldfishVote V) (t : Time),
    NamedRun.acceptsAt S rho i v (.gfVote u) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.gfVote u) = false →
      max t S.E.t_GST + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st (.gfVote u) = false →
      ∃ t', t ≤ t' ∧ t' < max t S.E.t_GST + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.gfVote u) t'
  relay_attest : ∀ v ∈ rho.honest, ∀ (i : Nat) (a : NamedAttestation V) (t : Time),
    NamedRun.acceptsAt S rho i v (.attest a) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.attest a) = false →
      max t S.E.t_GST + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st (.attest a) = false →
      ∃ t', t ≤ t' ∧ t' < max t S.E.t_GST + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.attest a) t'

structure NamedHealthyPrefixDelivery (S : Setup V) (rho : NamedRun V) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, NamedRun.emits S rho v o t →
    ∀ w ∈ rho.honest, t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st o = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t'
  relay_block : ∀ v ∈ rho.honest, ∀ (i : Nat) (B : NamedBlock V) (t : Time),
    NamedRun.acceptsAt S rho i v (.block B) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.block B) = false →
      t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.block B) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.block B) t'
  relay_gf_vote : ∀ v ∈ rho.honest, ∀ (i : Nat) (u : GoldfishVote V) (t : Time),
    NamedRun.acceptsAt S rho i v (.gfVote u) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.gfVote u) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.gfVote u) t'
  relay_attest : ∀ v ∈ rho.honest, ∀ (i : Nat) (a : NamedAttestation V) (t : Time),
    NamedRun.acceptsAt S rho i v (.attest a) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.attest a) = false →
      t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.attest a) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.attest a) t'


/-- Windowed fixed-cutoff delivery: the same three
transports as `NamedHealthyPrefixDelivery`, each restricted to emissions/accepts
sent no earlier than `lo`. Dropping the lower bound recovers the unwindowed
promise (`namedHealthyWindowDelivery_of_prefix`); the window is what a
post-`t_GST` open premise can actually establish, since `NamedSynchrony`
gives no guarantee at all for a send strictly before `t_GST`. -/
structure NamedHealthyWindowDelivery (S : Setup V) (rho : NamedRun V)
    (lo cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, NamedRun.emits S rho v o t →
    ∀ w ∈ rho.honest, lo ≤ t → t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st o = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t'
  relay_block : ∀ v ∈ rho.honest, ∀ (i : Nat) (B : NamedBlock V) (t : Time),
    NamedRun.acceptsAt S rho i v (.block B) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.block B) = false →
      lo ≤ t → t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.block B) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.block B) t'
  relay_gf_vote : ∀ v ∈ rho.honest, ∀ (i : Nat) (u : GoldfishVote V) (t : Time),
    NamedRun.acceptsAt S rho i v (.gfVote u) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.gfVote u) = false →
      lo ≤ t → t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.gfVote u) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.gfVote u) t'
  relay_attest : ∀ v ∈ rho.honest, ∀ (i : Nat) (a : NamedAttestation V) (t : Time),
    NamedRun.acceptsAt S rho i v (.attest a) t → ∀ w ∈ rho.honest,
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.attest a) = false →
      lo ≤ t → t + S.E.Δ ≤ cut →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.attest a) = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.attest a) t'

/-- The global named bundles, with no all-awake, open or cache premise. -/
structure NamedAdmissibleCore (S : Setup V) (rho : NamedRun V) : Prop extends
  NamedScheduleWellFormed S rho, NamedDeliveryWellFormed S rho,
  NamedRootCollisionFree S rho,
  NamedUnforgeable S rho, NamedSynchrony S rho

end DecoupledConsensusModel.Execution

end
