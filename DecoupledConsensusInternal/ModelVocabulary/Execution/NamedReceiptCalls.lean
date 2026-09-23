module
public import DecoupledConsensusModel
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun

@[expose] public section

/-! Actual named handler-call observers. Full object identity, event ownership,
carrier insertion gates and original list positions determine the calls.
The internal stored GF stage remains inside the existing block handler. -/
namespace DecoupledConsensusModel.Execution

namespace NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block call is a direct delivery or the actual self-emitted proposal.
The latter reads the clock-staged prefix, before later duties. -/
def blockCallAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.deliver v (.block B) t) ∧
    before = (NamedRun.stateBefore S rho i v).st) ∨
  ∃ t : Time, rho.events[i]? = some (.tick v t) ∧
    NamedObject.block B ∈ NamedRun.emittedAt S rho i v t ∧
    before = Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t

/-- Exact input to the j-th original full row of the F1 tail. -/
def f1Input (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) (j : Nat) :
    Protocol.NamedStore V :=
  Protocol.NamedAdmission.admit_rows S.hc (postCore S before B) (B.attestations.take j)

def carriedAttestationAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : Protocol.NamedStore V) : Prop :=
  blockCallAt S rho i v B before ∧ B ∉ before.bodies ∧
    B ∈ (postCore S before B).bodies ∧ B.attestations[j]? = some a

/-- Core insertion reaches the existing checked GF loop. Its exact internal
stored stage and list-prefix input are exposed only by the proof leaf. -/
def carriedGoldfishAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (u : GoldfishVote V) (before : Protocol.NamedStore V) : Prop :=
  blockCallAt S rho i v B before ∧ B.erase ∉ before.core.T ∧
    B.erase ∈ (postCore S before B).core.T ∧ B.gf_votes[j]? = some u

end NamedReceiptCalls

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Real calls include rejected row/vote calls. Pool acceptance is separate. -/
def actualHandlesAtIndex (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    NamedObject V → Prop
  | .block B => processesAtIndex S rho i v (.block B)
  | .gfVote u => processesAtIndex S rho i v (.gfVote u) ∨
      ∃ B j before, NamedReceiptCalls.carriedGoldfishAt S rho i v B j u before
  | .attest a => processesAtIndex S rho i v (.attest a) ∨
      ∃ B j before, NamedReceiptCalls.carriedAttestationAt S rho i v B j a before

def actualHandlesAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  actualHandlesAtIndex S rho i v o ∧
    ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = v ∧ e.time = t

def acceptsAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  actualHandlesAt S rho i v o t ∧
    NamedReceipt.processed (stateBefore S rho i v).st o = false ∧
    NamedReceipt.processed (stateBefore S rho (i + 1) v).st o = true

end NamedRun
end DecoupledConsensusModel.Execution

end
