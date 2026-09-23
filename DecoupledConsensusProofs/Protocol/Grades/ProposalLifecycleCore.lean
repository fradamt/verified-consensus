module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption

@[expose] public section

/-!
# Exact proposal lifecycle core

This low module packages only the local facts read by one Section 7
confirmation duty. It does not assume a canonical history or a suffix. The
public store theorem uses the existing exact confirmation-tick execution bridge.

**Named-runtime proof (design note).** The vote cone and
vote-name predicates are `Proofs.HealingSurface.NamedHonestVotesCone`/
`NamedHonestVotesName`, the duty block is a `NamedBlock V` (`B.erase` at every
erased use, rule C1), and the confirmation gate reads the prepared read's own
contract: `confAnchor`/`confWalk` become `namedConfirmationAnchor`/
`confWalkWith` at `NamedProfile.gradeContract (confirmationInputRead...).cache`
(rule, "anchor → `.anchor`"), because that contract — not
`GradeContract.current` — is what the named tick's `update_confirmation_with`
actually gates on (`Proofs.Optimistic.live_confirmed_eq_update`). `GenuineConfirmation`
(`Availability/Adoption.lean`) stays at its old, contract-free shape, so the
genuine-confirmation exit is restated here as `GenuineConfirmationWith`, its
exact contract-carrying analogue.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The exact confirmation-read facts for one honest proposal duty. This is
proof state only; it adds no protocol assumption.

**Named.** `B` is the named duty block (rule C1); `anchor`/`path` read the
prepared confirmation read's own contract anchor (rule ), not the
unparameterised `confAnchor`. -/
structure CanonicalProposalDutyAt
    (S : Setup V) (rho : Run V) (s : Slot) (B : NamedBlock V) : Prop where
  votes : Proofs.HealingSurface.NamedHonestVotesCone S rho s (fun X => X = B.erase)
  validLate : ∀ v ∈ rho.honest,
    Protocol.VoteSetValid S.E s
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
  anchor : ∀ v ∈ rho.honest,
    Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase
  path : ∀ v ∈ rho.honest, ∀ C : Block V,
    Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho v s)) C →
    C ≠ namedConfirmationAnchor S (confirmationInputRead S rho v s) →
    Block.Preceq C B.erase → C ∈ confTree (Proofs.Optimistic.confStore S rho v s)
  resolve : ∀ v ∈ rho.honest,
    Proofs.Optimistic.HeadsResolveIn S rho s
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block
  counted : ∀ v ∈ rho.honest, ∀ u : GoldfishVote V,
    u.slot = s → u.val_index ∈ rho.honest →
    u.val_index ∈ S.E.committee s →
    rho.emits S u.val_index (Object.gfVote u) (Protocol.vote_time S.E s) →
    u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s

/-- Build the duty package from exact proposal provenance, exact honest vote
names, and the five local confirmation-store facts. -/
def CanonicalProposalDutyAt.ofLocalFacts
    (S : Setup V) (rho : Run V) (s : Slot) (B : NamedBlock V)
    (hrun : RunBlock S rho B)
    (hnames : Proofs.HealingSurface.NamedHonestVotesName S rho s B.erase)
    (hvalidLate : ∀ v ∈ rho.honest,
      Protocol.VoteSetValid S.E s
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s))
    (hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase)
    (hpath : ∀ v ∈ rho.honest, ∀ C : Block V,
      Block.Preceq
        (namedConfirmationAnchor S (confirmationInputRead S rho v s)) C →
      C ≠ namedConfirmationAnchor S (confirmationInputRead S rho v s) →
      Block.Preceq C B.erase → C ∈ confTree (Proofs.Optimistic.confStore S rho v s))
    (hresolve : ∀ v ∈ rho.honest,
      Proofs.Optimistic.HeadsResolveIn S rho s
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho v s).timestamp_block)
    (hcounted : ∀ v ∈ rho.honest, ∀ u : GoldfishVote V,
      u.slot = s → u.val_index ∈ rho.honest →
      u.val_index ∈ S.E.committee s →
      rho.emits S u.val_index (Object.gfVote u) (Protocol.vote_time S.E s) →
      u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) :
    CanonicalProposalDutyAt S rho s B where
  votes := Proofs.Optimistic.honestVotesCone_of_name S rho s rfl hrun hnames
  validLate := hvalidLate
  anchor := hanchor
  path := hpath
  resolve := hresolve
  counted := hcounted

/-- An exact honest-vote cone is the route-independent exact vote-name
contract. -/
theorem honestVotesName_of_exactCone
    (S : Setup V) (rho : Run V) (s : Slot) (B : Block V)
    (hcone : Proofs.HealingSurface.NamedHonestVotesCone S rho s (fun X => X = B)) :
    Proofs.HealingSurface.NamedHonestVotesName S rho s B := by
  intro v hv hcommittee
  obtain ⟨X, hXB, -, hemit⟩ := hcone v hv hcommittee
  rw [hXB] at hemit
  exact hemit

private theorem proposedBlock_find_of_dutyExecution
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {B : NamedBlock V}
    (hexec : CanonicalProposalDutyAt S rho s B)
    {v : V} (hv : v ∈ rho.honest) :
    Block.find? (Proofs.Optimistic.confStore S rho v s).T B.erase.root = some B.erase := by
  classical
  have hcard : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hmajority := hcom s
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  have hxCommittee : x ∈ S.E.committee s := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hXB, hXrun, hXemit⟩ :=
    hexec.votes x hxHonest hxCommittee
  rw [hXB] at hXemit
  exact (hexec.resolve v hv B.erase
    ⟨x, hxHonest, hxCommittee, ⟨X, hXB, hXrun⟩, hXemit⟩).1

private theorem honestSupport_of_dutyExecution
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {B : NamedBlock V}
    (hexec : CanonicalProposalDutyAt S rho s B)
    {v : V} (hv : v ∈ rho.honest) :
    HonestSupport S.E (Proofs.Optimistic.confStore S rho v s).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      s rho.honest B.erase := by
  have hnames := honestVotesName_of_exactCone S rho s B.erase hexec.votes
  have hfind := proposedBlock_find_of_dutyExecution S hcom hexec hv
  exact Proofs.Optimistic.honestSupport_of_names
    S rho s B.erase hcom hnames hfind (hexec.counted v hv)

/-- The exact Section 7 confirmation call selects the duty block, under the
contract the confirming node's own prepared read carries. -/
theorem updateConfirmation_eq_proposedBlock_of_dutyExecution
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {B : NamedBlock V}
    (hexec : CanonicalProposalDutyAt S rho s B)
    {v : V} (hv : v ∈ rho.honest) :
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).live_confirmed = B.erase := by
  have hsupport := honestSupport_of_dutyExecution S hcom hexec hv
  exact live_confirmed_eq_with
    (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
    S.E S.hc (Proofs.Optimistic.confStore S rho v s)
    s rho.honest B.erase hsupport (hexec.validLate v hv)
      (hexec.anchor v hv) (hexec.path v hv)

/-- The contract-carrying analogue of `Adoption.GenuineConfirmation`: the
selected value is the contract's own composed walk, and that walk cleared the
confirmation gate. `Adoption.GenuineConfirmation` stays at the unparameterised
`GradeContract.current` walk, which the named tick does not run. -/
structure GenuineConfirmationWith (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Prop where
  selected : (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B
  genuine : confEligible E st s (confWalkWith contract E hc st s) = true

/-- Byte-parallel to `confEligible_confWalk_iff`, at the contract-carrying
walk: the guard-eligibility argument is `Protocol.ghost_eligible`, which is
generic in the walk's starting block. -/
private theorem confEligible_confWalkWith_iff
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) :
    confEligible E st s (confWalkWith contract E hc st s) = true ↔
      (confWalkWith contract E hc st s ≠ confAnchorWith contract E hc st ∨
        confEligible E st s (confAnchorWith contract E hc st) = true) := by
  constructor
  · intro h
    by_cases hA : confWalkWith contract E hc st s = confAnchorWith contract E hc st
    · exact Or.inr (hA ▸ h)
    · exact Or.inl hA
  · intro h
    rcases ghost_eligible (confAnchorWith contract E hc st) (confTree st)
      (confScore E st s) (confEligible E st s) with hw | hw
    · have hw' : confWalkWith contract E hc st s = confAnchorWith contract E hc st := hw
      rcases h with hne | hel
      · exact absurd hw' hne
      · rw [hw']
        exact hel
    · exact hw

/-- The exact selected duty block is a genuine Section 7 confirmation, under
the confirming node's own prepared-read contract. -/
theorem genuineConfirmation_of_dutyExecution
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {B : NamedBlock V}
    (hexec : CanonicalProposalDutyAt S rho s B)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s B.erase := by
  have hsupport := honestSupport_of_dutyExecution S hcom hexec hv
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s
  have hanchorEligible : confEligible S.E
      (Proofs.Optimistic.confStore S rho v s) s
      (confAnchorWith
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s)) = true := by
    simp only [confEligible, decide_eq_true_eq, confCount, confScore]
    exact hsupport.eligible hN (hexec.validLate v hv) (hexec.anchor v hv)
  have hwalkEligible : confEligible S.E
      (Proofs.Optimistic.confStore S rho v s) s
      (confWalkWith
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s) s) = true :=
    (confEligible_confWalkWith_iff
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).2 (Or.inr hanchorEligible)
  exact ⟨updateConfirmation_eq_proposedBlock_of_dutyExecution
    S hcom hexec hv, hwalkEligible⟩

/-- The public confirmation-time store records the exact duty selection. -/
theorem storeAt_liveConfirmed_eq_proposedBlock_of_dutyExecution
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {B : NamedBlock V}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hexec : CanonicalProposalDutyAt S rho s B)
    {v : V} (hv : v ∈ rho.honest) :
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed
      = B.erase := by
  rw [Proofs.Optimistic.live_confirmed_eq_update
    S adm.toNamedScheduleWellFormed hv s hhor]
  exact updateConfirmation_eq_proposedBlock_of_dutyExecution
    S hcom hexec hv

end Protocol
end DecoupledConsensusModel

end
