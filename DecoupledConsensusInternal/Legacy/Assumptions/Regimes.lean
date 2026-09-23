module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.SafetyRegimes
public import DecoupledConsensusInternal.Legacy.Interface
public import DecoupledConsensusInternal.Legacy.Definitions.NamedOutageEntry

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Assumption regimes for the final contracts
These records group existing execution assumptions. They contain no assumed
recovery invariant, grade formation, canonicality, or liveness result. -/



namespace DecoupledConsensusModel
namespace Statements
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Weak participation from genesis. Execution validity and partial synchrony
are separate visible premises. There is no accountable or one-third bound. -/
structure WeakGenesis (S : Setup V) (rho : Run V) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  committees : HonestCommittees S rho.honest
  gstZero : S.E.t_GST = 0
  windows : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r

/-- The finite strong prefix ends at the specified, bounded recovery-search
endpoint. Execution validity, partial synchrony, and full participation from
GST are
separate visible premises. This record does not assume that recovery succeeds. -/
structure StrongRecoveryPrefix (S : Setup V) (rho : Run V)
    (rGST gap : Round) (extra : Nat) (n : Round) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  allAwake : ∀ v ∈ rho.honest, ∀ r : Round, S.E.t_GST ≤ S.a r → S.a r ≤ rho.horizon →
    (S.node v).awake r = true
  committees : HonestCommittees S rho.honest
  belowThird : BelowOneThird S rho.honest
  recurrence : MultiProposerRecurrence S rho gap S.E.t_GST
  timeout : TimeoutDelayBound S extra
  postGST : S.E.t_GST ≤ S.a rGST
  start : BoundedPhaseStart S rho rGST gap extra n
  horizon : rho.horizon = S.a (n + gap)

/-- A continuation agrees through the end of the strong prefix. Execution
validity and partial synchrony are separate visible premises. After the
endpoint, only SG awake-window majority is required. Its honest set can differ.
The continuation horizon reaches `healingBoundaryTime S endRound`, not only
the action time `S.a endRound`. -/
structure WeakContinuation (S : Setup V) (source rho : Run V)
    (endRound : Round) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  committees : HonestCommittees S rho.honest
  accountable : SlashableBound S rho
  agrees : AgreesUntil source rho (S.a endRound)
  covered : healingBoundaryTime S endRound ≤ rho.horizon
  windows : ∀ r, endRound < r → S.a (r - 1) ≤ rho.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r

/-- The current finality-liveness regime. Execution validity, partial
synchrony, and full participation from GST are separate visible premises. The
timeout
condition is stated separately. -/
structure StrongFinalityRun (S : Setup V) (rho : Run V) (gap : Round) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  allAwake : ∀ v ∈ rho.honest, ∀ r : Round, S.E.t_GST ≤ S.a r → S.a r ≤ rho.horizon →
    (S.node v).awake r = true
  committees : HonestCommittees S rho.honest
  belowThird : BelowOneThird S rho.honest
  recurrence : ProposerOpeningCarrierRecurrence S rho gap S.E.t_GST
  gapBound : gap + 2 ≤ S.cfg.K

end Statements
end DecoupledConsensusModel

/-! # Standard-vocabulary regimes

The historical records above remain available to the proof layer. The records
below are the protocol-facing regime vocabulary used by `Claims.lean`.
-/

namespace DecoupledConsensusModel
namespace Statements

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every slot committee has a strict honest majority by count. -/
def HonestCommittees (I : Interface V) (H : Finset V) : Prop :=
  ∀ s : Slot, (I.committee s).card < 2 * ((I.committee s) ∩ H).card

/-- No evidence occurs between two certificates assembled from the run. -/
def SlashableBound (I : Interface V) (rho : Run V) : Prop :=
  ∀ c c', I.inRun rho c → I.inRun rho c' → ¬ I.evidence c c'

/-- Sleepy participation from `t₀`. -/
structure SleepyRegime (S : Setup V) (I : Interface V) (C : Constants) (rho : Run V)
    (t₀ : Time) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  gst : S.E.t_GST ≤ t₀
  committees : HonestCommittees I rho.honest
  /-- The window for round `r` is required when round `r` acts at or after `t₀`. -/
  windows : ∀ r : Round, 0 < r → t₀ ≤ S.a r → S.a (r - 1) ≤ rho.horizon →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest C.windowRounds r

/-- Full BFT participation from GST, with `t₀` at or after GST. -/
structure BFTRegime (S : Setup V) (I : Interface V) (rho : Run V) (t₀ : Time) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  gst : S.E.t_GST ≤ t₀
  committees : HonestCommittees I rho.honest
  belowThird : BelowOneThird S rho.honest
  allAwake : ∀ v ∈ rho.honest, ∀ r : Round, S.E.t_GST ≤ S.a r → S.a r ≤ rho.horizon →
    (S.node v).awake r = true

/-- A finite strong recovery prefix. -/
structure RecoveryRegime (S : Setup V) (I : Interface V) (C : Constants) (rho : Run V)
    (t₀ : Time) (gap : Nat) (extra : Nat) : Prop
    extends BFTRegime S I rho t₀ where
  recurrence : MultiProposerRecurrence S rho gap S.E.t_GST
  timeout : TimeoutDelayBound S extra
  horizon : rho.horizon = C.prefixEnd t₀ gap extra

/-- A whole-run finality regime. -/
structure FinalityRegime (S : Setup V) (I : Interface V) (rho : Run V) (t₀ : Time)
    (gap : Nat) (extra : Nat) : Prop
    extends BFTRegime S I rho t₀ where
  recurrence : ProposerOpeningCarrierRecurrence S rho gap S.E.t_GST
  gapBound : gap + 2 ≤ S.cfg.K
  timeout : TimeoutDelayBound S extra

/-- A continuation agrees with a prefix through `cut` and reaches `upto`. -/
structure Continues (source rho : Run V) (cut upto : Time) : Prop where
  agrees : AgreesUntil source rho cut
  covered : upto ≤ rho.horizon

/-- The run is recovered at a time, either at genesis or after a recovery prefix. -/
inductive RecoveredBy (S : Setup V) (I : Interface V) (C : Constants) (rho : Run V) :
    Time → Prop
  | genesis : RecoveredBy S I C rho 0
  | recovered {source : Run V} {t₀ : Time} {gap extra : Nat} :
      RecoveryRegime S I C source t₀ gap extra →
      Continues source rho (C.prefixEnd t₀ gap extra) (C.recoveryEnd t₀ gap extra) →
      SlashableBound I rho →
      RecoveredBy S I C rho (C.recoveryEnd t₀ gap extra)

/-- The outage regime on `[b₀, b₁]`. -/
structure OutageRegime (S : Setup V) (I : Interface V) (C : Constants) (rho : Run V)
    (b₀ b₁ : Time) : Prop where
  execution : ExecutionValid S rho
  synchrony : PartialSynchrony S rho
  gst : S.E.t_GST ≤ b₁
  committees : HonestCommittees I rho.honest
  healthy : HealthyPrefixDelivery S rho b₀
  interval : 0 ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  boundaryPublic : PublicTime S b₀
  /-- At every covered round, honest weight awake at the previous round
  outweighs faulty weight plus honest weight awake only in older window rounds.
  This is stated on the environment's awake profile; action attestations are a
  consequence of being awake. -/
  participation : NamedOutageEntry.AwakeGradeMajorityThroughout S rho

end Statements
end DecoupledConsensusModel

end
