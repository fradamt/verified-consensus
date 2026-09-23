module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedOutageEntry
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow

@[expose] public section

/-! Proof-side named outage read helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Participation throughout the covered run, including before the outage. -/
def OutageSleepyThroughout (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ r, 0 < r → RoundCovered S rho r →
    AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r

/-- Scan the actual full named tick emissions at the claimed round action. -/
def emittedInRound (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) : Bool :=
  (List.range rho.events.length).any (fun i =>
    match rho.events[i]? with
    | some (.tick u t) =>
      if u = v ∧ t = S.a k then
        (NamedRun.emittedAt S rho i v t).any (fun o =>
          match o with
          | .attest a => decide (a.val_index = v ∧ a.round = k)
          | _ => false)
      else false
    | _ => false)

def honestRoundVoters (S : Setup V) (rho : NamedRun V) (k : Round) : Finset V :=
  rho.honest.filter (fun v => emittedInRound S rho v k)

/-- All honest voters in the older eligible rounds [r-eta,r-2]. -/
def historicalHonestVoters (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  ((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => honestRoundVoters S rho k)

/-- Historical union minus actual voters of the preceding round. -/
def staleHistoricalVoters (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  historicalHonestVoters S rho r \ honestRoundVoters S rho (r - 1)

/-- The selected weighted inequality with fixed honest membership.
This does not assert positive support or body open at any reader. -/
def GradeFormingMajority (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
      staleHistoricalVoters S rho r) <
    S.E.electorate.weightOf (honestRoundVoters S rho (r - 1))

def GradeFormingThroughout (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ r, 0 < r → RoundCovered S rho r → GradeFormingMajority S rho r



/-- The confirmation input at a support-cutoff tick: clock update and the
same prepared cache, with the incoming signing record. The absence of the
proposal and vote branches at such a tick is a proof obligation. -/
def confirmationReadFrom (S : Setup V) (before : NamedNodeState V) (t : Time) :
    NamedNodeState V :=
  Execution.NamedActionReads.confirmationReadFrom S before t

/-- The strict read followed by support-cutoff clock/cache staging. Only the
support-cutoff and round-action times below are used as confirmation reads. -/
def confirmationReadAt (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    NamedNodeState V :=
  Execution.NamedActionReads.confirmationReadAt S rho v t


def preparedCache (S : Setup V) (before : NamedNodeState V) (t : Time) : Cache V :=
  Execution.NamedActionReads.preparedCache S before t

def actionReadFrom (S : Setup V) (before : NamedNodeState V) (r : Round) :
    NamedNodeState V :=
  Execution.NamedActionReads.actionReadFrom S before r

def actionReadAt (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedNodeState V :=
  Execution.NamedActionReads.actionReadAt S rho v r

end DecoupledConsensusModel.Internal.NamedOutageEntry

end
