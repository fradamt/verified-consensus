module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedActionReads
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible
public import DecoupledConsensusModel.Protocol.Evidence
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight

@[expose] public section

/-!
# Named outage execution and awake participation — review draft

Definitions only. No named outage theorem is claimed. The named environmental
bundles retain their checked receipt, deadline and horizon formulas. The run
and each tick stage are computed from NamedRun and NamedNode with the supplied
Setup. The public participation inequality counts who is awake; the proof layer
derives the corresponding emissions.

The current phase offsets (early, late, domain), in Delta units, are
G2=(-5,-1,-1), G1=(-4,-2,0), G0=(-3,-3,+1). All phase formulas below use
DecoupledConsensusModel.Protocol directly; no replacement schedule is defined here.
-/
namespace DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-- Whole-run accountable bound on full named run-block chains. Only the
E1/E2 evidence view erases rows; the quantified block scope stays named.
 1286 follows Stage L, post-recovery-safety-plan.md section 47y
(line 5126): the accountable bound applies to the whole run. E1 remains
height-wide. This is not a bound on total faulty weight. -/
abbrev SlashableBound (S : Setup V) (rho : NamedRun V) : Prop :=
  Execution.SlashableBound S rho

/-- One outage with healthy deadlines through `b0` and recovery by `b1`.

The premises are the four execution-validity families, explicit partial
synchrony, a nonnegative interval inside the run horizon, healthy-prefix
delivery through `b0`, `t_GST ≤ b1`, and a public `Δ`-grid boundary. The setup
supplies `R ≥ 3` through `HealConfig.R_ge_three`.
The model has one GST, so the interval `[b0,b1]` is the initial asynchronous
period ending by `b1`; runs with `t_GST < b0` satisfy the premises with ordinary
synchrony inside the interval. An arbitrary later temporary outage is not
modelled. Together with `FormationMargin` and `RetentionDuration`, the earliest
`b0` and latest `b1` are at most `Δ · (4 · R · η_SG − 13)` apart; a strict
interval is possible exactly when `13 < 4 · R · η_SG`. -/
structure OutageExecution (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) : Prop where
  execution : Execution.ExecutionValid S rho
  synchrony : Execution.PartialSynchrony S rho
  interval : 0 ≤ b0 ∧ b0 ≤ b1 ∧ b1 ≤ rho.horizon
  healthy : NamedHealthyPrefixDelivery S rho b0
  
  gst : S.E.t_GST ≤ b1
  
  boundaryPublic : Execution.PublicTime S b0

def RoundCovered (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  (0 ≤ S.a r ∧ S.a r ≤ rho.horizon) ∨
    ∃ p : Phase, 0 ≤ domain S.E S.hc r p ∧ domain S.E S.hc r p ≤ rho.horizon

/-- Honest validators awake at round `k`. -/
def honestAwakeAt (S : Setup V) (rho : NamedRun V) (k : Round) : Finset V :=
  rho.honest.filter (fun v => (S.node v).awake k)

/-- Honest validators awake in an older window round `[r - η_SG, r - 2]` but not at `r - 1`. -/
def staleAwake (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  (((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => honestAwakeAt S rho k)) \ honestAwakeAt S rho (r - 1)


/-- The participation premise of the outage result: at
every covered round, honest weight awake at the previous round outweighs all
faulty weight plus honest weight awake only in older window rounds. It is a
stronger sleepy condition, stated on who is awake when; the protocol's
attestations are a consequence of being awake. -/
def AwakeGradeMajority (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪ staleAwake S rho r) <
    S.E.electorate.weightOf (honestAwakeAt S rho (r - 1))

def AwakeGradeMajorityThroughout (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ r, 0 < r → RoundCovered S rho r → AwakeGradeMajority S rho r

end DecoupledConsensusModel.Internal.NamedOutageEntry

end
