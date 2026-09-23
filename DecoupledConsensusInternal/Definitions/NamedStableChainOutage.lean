module
public import DecoupledConsensusInternal.ModelVocabulary
public import Mathlib.Data.Finset.Max
public import DecoupledConsensusInternal.Legacy.Definitions.NamedStableChainOutageInternal
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry

@[expose] public section

/-! Proof-side outage helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal.NamedStableChainOutage
open Execution NamedOutageEntry DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]



/-- The exact optional SG candidate in the named frame contract. -/
def activeG2 (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  DecoupledConsensusModel.Protocol.frameSGCandidate n.cache S.E S.hc n.st.core.toHealing n.st.core.s

/-- Reuse the existing optional-G2 confirmation choice on that fixed read. -/
def confirmationCandidate (S : Setup V) (n : NamedNodeState V) (s : Slot) : Option (Block V) :=
  P1FrameOperations.confirmationCandidate (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core s

/-- Every real candidate call, including one that leaves an old descendant fixed. -/
def CandidateWritten (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) (B : Block V) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
    let n := confirmationReadFrom S (NamedRun.stateBefore S rho i v) t
    let s := S.E.slotOf t
    0 < s ∧ t = Protocol.support_cutoff S.E s ∧
    confirmationCandidate S n (s - 1) = some B


def sgRoot (S : Setup V) (n : NamedNodeState V) : Block V :=
  Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing (S.hc.round_of n.st.core.s)

def goldfishChoiceAt (S : Setup V) (n : NamedNodeState V) (s : Slot) : Block V × Bool :=
  P1FrameOperations.goldfishChoiceAt (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core s

def G2EstablishesAt (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) (P : Block V) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
    let before := NamedRun.stateBefore S rho i v
    let n := confirmationReadFrom S before t
    let s := S.E.slotOf t
    0 < s ∧ t = Protocol.support_cutoff S.E s ∧
    (∃ G, activeG2 S n = some G ∧ Block.Preceq P G) ∧
    Block.Preceq P (NamedNode.tick S v before t).1.st.core.latest_confirmed


/-- Stability is read before the confirmation and attestation duties at a_s.
Proof-layer seed (moved from the Statements layer): the public
outage statement is seeded by the stable output instead. -/
def roundConfirmationRead (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) :
    NamedNodeState V :=
  confirmationReadAt S rho v (S.a s)

def stableAt (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) (P : Block V) : Prop :=
  ∃ G, activeG2 S (roundConfirmationRead S rho v s) = some G ∧ Block.Preceq P G


/-- Proof-layer round-form margins and outputs (moved from the Statements layer
,; the public statement is in time form).
Addendum 34 10: the round after the stable round
completes its action, and its rows are delivered, before the outage; hence the
first included round is at least `s + 2`. -/
def FormationMargin (S : Setup V) (s : Round) (b0 : Time) : Prop :=
  S.a (s + 1) + S.E.Δ ≤ b0

/-- The outage and the recovery delay end before fresh round-`s` support
expires, and the same deadline is inside the finite run. -/
def RetentionDuration (S : Setup V) (rho : NamedRun V) (s : Round)
    (b1 : Time) : Prop :=
  b1 + S.E.Δ ≤ early S.E S.hc (s + S.hc.η_SG + 1) .g2 ∧
    b1 + S.E.Δ ≤ rho.horizon


/--: stable user outputs persist after the outage, for every honest read
from `b0` through the run horizon. The bounded `StableUserOutputs` form is
retained for the proof-layer outage window. -/
def StableUserOutputsFrom (S : Setup V) (rho : NamedRun V) (b0 : Time) (P : Block V) :
    Prop :=
  ∀ w ∈ rho.honest, ∀ t, b0 ≤ t → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t w
    Block.Preceq P (Protocol.get_stable n.st.core) ∧
    (∀ G, activeG2 S n = some G → Block.Preceq P G) ∧
    (∀ u, b0 ≤ u → u ≤ t → ∀ B, CandidateWritten S rho w u B → Block.Preceq P B)

def boundaryFrontier (S : Setup V) (rho : NamedRun V) (b0 : Time) (v : V) : Height :=
  (NamedRun.stateBeforeTime S rho b0 v).st.core.h_max

def LeadingAtBoundary (S : Setup V) (rho : NamedRun V) (b0 : Time) (P : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∃ W : NamedBlock V,
    W ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies ∧
    Block.Preceq P W.erase ∧
    (Protocol.derive_named S.E S.cfg W).h = boundaryFrontier S rho b0 v

def StableEntryAt (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (v : V) (s : Round) (P : Block V) : Prop :=
  stableAt S rho v s P ∧ LeadingAtBoundary S rho b0 P

def NoHonestConflictAbove (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (P : Block V) : Prop :=
  (∀ Pn : NamedBlock V, NamedRun.blockInRun S rho Pn → Pn.erase = P →
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → t < b0 →
      ∀ h root timeout, a.height_pair = .vote h root timeout →
        ∀ entry : NamedBlock V, NamedRun.blockInRun S rho entry → entry.root = root →
          NamedBlock.compatible Pn entry = true) ∧
  (∀ Pn : NamedBlock V, NamedRun.blockInRun S rho Pn → Pn.erase = P →
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → t < b0 →
      ∀ h root, a.finality_pair = some ⟨h, root⟩ →
        ∀ entry : NamedBlock V, NamedRun.blockInRun S rho entry → entry.root = root →
          NamedBlock.compatible Pn entry = true)

def formationConfirmationTime (S : Setup V) (r : Round) : Time :=
  Protocol.support_cutoff S.E (S.hc.opening_slot r)

def formationConfirmationRead (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedNodeState V :=
  confirmationReadAt S rho v (formationConfirmationTime S r)

def positiveSupportersAt (S : Setup V) (n : NamedNodeState V) (r : Round) (P : Block V) :
    Finset V :=
  let st := n.st.core
  Finset.univ.filter (fun u => positive st.toHealing.gradeView st.F S.hc.η_SG r
    (early S.E S.hc r .g2) (late S.E S.hc r .g2) u P = true)

def latestEarlyInputsAt (S : Setup V) (n : NamedNodeState V) (r : Round) (u : V) :
    Finset (Protocol.SGVote V) :=
  let st := n.st.core
  let inputs := DecoupledConsensusModel.Protocol.interpretedInputs st.toHealing.gradeView st.F S.hc.η_SG r
    (early S.E S.hc r .g2) u
  inputs.filter (fun a => ∀ x ∈ inputs, x.round ≤ a.round)

def supporterRoundsAt (S : Setup V) (n : NamedNodeState V) (r : Round) (P : Block V) :
    Finset Round :=
  (positiveSupportersAt S n r P).biUnion
    (fun u => (latestEarlyInputsAt S n r u).image (fun a => a.round))

def kMinAt (S : Setup V) (n : NamedNodeState V) (r : Round) (P : Block V) : Option Round :=
  let rounds := supporterRoundsAt S n r P
  if h : rounds.Nonempty then some (rounds.min' h) else none

def kMin (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) (P : Block V) : Option Round :=
  kMinAt S (roundConfirmationRead S rho v s) s P

def formationKMin (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) (P : Block V) :
    Option Round :=
  kMinAt S (formationConfirmationRead S rho v r) r P

private theorem margin_gap (X D : Int) (hD : 0 ≤ D) :
    X + 2 * D + D ≤ X + 6 * D + D := by omega

theorem old_margin_of_new (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) :
    formationConfirmationTime S (s + 1) + S.E.Δ ≤ b0 := by
  refine le_trans ?_ hmargin
  show Protocol.support_cutoff S.E (S.hc.opening_slot (s + 1)) + S.E.Δ ≤
    S.hc.a S.E.Δ (s + 1) + S.E.Δ
  simp only [Protocol.support_cutoff, Env.t, slotStart, Protocol.HealConfig.a]
  exact margin_gap _ _ (le_of_lt S.E.Δ_pos)

abbrev StableRetentionBudget (S : Setup V) (rho : NamedRun V) (_v : V) (s : Round)
    (_P : Block V) (b1 : Time) : Prop :=
  RetentionDuration S rho s b1

def BoundaryProtectionCases (S : Setup V) (rho : NamedRun V) (b0 : Time) (P : Block V) : Prop :=
  ∀ v ∈ rho.honest,
    let n := NamedRun.stateBeforeTime S rho b0 v
    Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
      ∃ G, activeG2 S n = some G ∧ Block.Preceq P G

def EntryPrefixOutputs (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V) :
    Prop :=
  ∀ w ∈ rho.honest, ∀ t, b0 ≤ t → t ≤ b1 + S.E.Δ → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t w
    (Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
      ∃ G, activeG2 S n = some G ∧ Block.Preceq P G) ∧
    Block.Preceq P (sgRoot S n) ∧
    Block.Preceq P (Protocol.get_stable n.st.core) ∧
    (∀ u, b0 ≤ u → u ≤ t → ∀ B, CandidateWritten S rho w u B → Block.Preceq P B)

def StableUserOutputs (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V) :
    Prop :=
  ∀ w ∈ rho.honest, ∀ t, b0 ≤ t → t ≤ b1 + S.E.Δ → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t w
    Block.Preceq P (Protocol.get_stable n.st.core) ∧
    (∀ G, activeG2 S n = some G → Block.Preceq P G) ∧
    (∀ u, b0 ≤ u → u ≤ t → ∀ B, CandidateWritten S rho w u B → Block.Preceq P B)

def HonestConfirmedAtOrAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t < b0 → s ≤ a.round →
    ∀ key, a.confirmed = some key →
      ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
        Block.Preceq P K.erase

def HonestHeadHeldAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t + S.E.Δ ≤ b0 → s ≤ a.round →
    ∀ reader ∈ rho.honest, ∀ cut : Time, t + S.E.Δ ≤ cut →
      Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F P →
      ∀ key, a.confirmed = some key →
        ∃ H : NamedBlock V,
          H ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies ∧ H.root = key ∧
          Block.compatible H.erase
            (NamedRun.stateBeforeTime S rho cut reader).st.core.F = true ∧
          ∀ gamma : Time, t + S.E.Δ ≤ gamma →
            stampedBefore (NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_block
              gamma H.erase = true

def ConfirmationCoverageBefore (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ t : Time,
    S.a s ≤ t → t < b0 →
    0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
    Block.Preceq P (sgRoot S (confirmationReadAt S rho w t)) ∧
    ∀ G, activeG2 S (confirmationReadAt S rho w t) = some G → Block.Preceq P G

def PreBoundaryFrames (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ q : Round, s + 1 ≤ q → S.a q < b0 →
    let n := NamedRun.readAt S rho (domain S.E S.hc q .g1) w
    Block.Preceq P n.st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q).g2 = some (some raw) ∧
          Block.Preceq P raw

def HonestConfirmedAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  HonestConfirmedAtOrAbove S rho b0 s P ∧ (HonestHeadHeldAbove S rho b0 s P ∧
    (ConfirmationCoverageBefore S rho b0 s P ∧ PreBoundaryFrames S rho b0 s P))

def OutageEntryPreservation (S : Setup V) : Prop :=
  ∀ rho b0 b1 v s P,
    OutageExecution S rho b0 b1 → NamedOutageEntry.SlashableBound S rho →
    OutageSleepyThroughout S rho → GradeFormingThroughout S rho →
    v ∈ rho.honest → FormationMargin S s b0 → stableAt S rho v s P →
    NoHonestConflictAbove S rho b0 P → HonestConfirmedAbove S rho b0 s P →
    StableRetentionBudget S rho v s P b1 →
    EntryPrefixOutputs S rho b0 b1 P

def StableChainOutageResilienceFromClauses (S : Setup V) : Prop :=
  ∀ rho b0 b1 v s P,
    OutageExecution S rho b0 b1 → NamedOutageEntry.SlashableBound S rho →
    OutageSleepyThroughout S rho → GradeFormingThroughout S rho →
    v ∈ rho.honest → FormationMargin S s b0 → stableAt S rho v s P →
    NoHonestConflictAbove S rho b0 P → HonestConfirmedAbove S rho b0 s P →
    StableRetentionBudget S rho v s P b1 →
    StableUserOutputs S rho b0 b1 P

end DecoupledConsensusModel.Internal.NamedStableChainOutage

end
