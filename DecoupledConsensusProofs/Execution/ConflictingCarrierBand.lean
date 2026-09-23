module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Objects.AwakeWindowQuorum

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedConflictingCarrierBand
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

-- A quorum contains an honest signer when faulty weight is below the
-- quorum threshold.
-- The outer sleepy condition supplies the required honest participation.
-- `Proofs.NamedOutageInputs.boundary_faulty_lt_quorum` supplies the
-- faulty-weight bound at the outage boundary.
private theorem quorum_honest_member (S : Setup V) (rho : NamedRun V)
    (Q : Finset V) (hQ : S.E.electorate.IsQuorum Q)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ signer ∈ Q, signer ∈ rho.honest := by
  by_contra hn
  have hsub : Q ⊆ Finset.univ \ rho.honest := by
    intro signer hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hn ⟨signer, hs, hh⟩⟩
  have hm := S.E.electorate.weightOf_mono hsub
  have hq : S.E.q ≤ S.E.electorate.weightOf Q := hQ
  omega

omit [Fintype V] in
private theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
private theorem named_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
    subst B
    exact hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBC
    rcases hBC with rfl | hparent
    · exact hAB
    · exact named_extend s root votes support rows proposer (ih hparent)

omit [DecidableEq V] [Fintype V] in
private theorem matching_vote (a : NamedAttestation V) (h : Height) (root : BlockId)
    (hm : a.height_pair.matchesEntry h root = true) :
    ∃ timeout : Bool, a.height_pair = .vote h root timeout := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height entry timeout =>
    have heq : height = h ∧ entry = root := by
      simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨timeout, rfl⟩

/-- Produce the intrinsic band from actual prior all-height entry history.
The crossing quorum's honest member is obtained from the existing sleepy
window in round s+1. No additional bound on faulty weight is an input.
PriorCarrierRows remains quantified inside the target. -/
theorem intrinsic_conflicting_carrier_band
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hhistory : IntrinsicHighEntryHistory S rho P r) :
    IntrinsicConflictingCarrierBand S rho P r := by
  have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin
    hsleep
  intro B hB hPrior hConflict
  by_contra hNot
  let H := (derive_named S.E S.cfg P).h + 1
  have hPassed : H < (derive_named S.E S.cfg B).h := Nat.lt_of_not_ge hNot
  have hPositive : 1 ≤ H := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨X, hXB, _hXHeight, Q, hQ, hRows⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg B H hPositive hPassed
  obtain ⟨signer, hSignerQ, hSignerHon⟩ := quorum_honest_member S rho Q hQ hbad
  obtain ⟨carrier, a, hCarrier, hRow, hSigner, hMatch⟩ := hRows signer hSignerQ
  have haHon : a.val_index ∈ rho.honest := by
    simpa only [hSigner] using hSignerHon
  obtain ⟨har, hem⟩ := ((hPrior carrier hCarrier).2 a hRow).2 haHon
  obtain ⟨timeout, hVote⟩ := matching_vote a H X.root hMatch
  obtain ⟨i, source, entry, hSigned, hSourceHeight, hEntryRoot⟩ :=
    Proofs.NamedIntrinsicEntry.emitted_height_signed_source S rho hem hVote
  have hEntryBefore : HonestEntryBefore S rho r H entry :=
    ⟨i, a, source, haHon, har, hSigned, hSourceHeight⟩
  have hEntryCompatible : NamedBlock.compatible P entry = true :=
    hhistory H entry hEntryBefore
  rcases hSigned with ⟨_, _, _, hSourceHeld, _, hEntrySource, _, hEntryHeight, _⟩
  have hPEntry : NamedBlock.Preceq P entry := by
    rcases (show NamedBlock.Preceq P entry ∨ NamedBlock.Preceq entry P by
      simpa only [NamedBlock.compatible, Bool.or_eq_true] using hEntryCompatible) with
      hAbove | hAncestor
    · exact hAbove
    · have hle := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hAncestor
      rw [hEntryHeight, hSourceHeight] at hle
      have hStrict : (derive_named S.E S.cfg P).h < H := Nat.lt_succ_self _
      exact False.elim ((Nat.not_le_of_gt hStrict) hle)
  have hPre : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hSourceHeld
  have hSourceScope : NamedRun.blockInRun S rho source :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho haHon i hPre)
  have hEntryEq : entry = X :=
    hexec.core.toNamedRootCollisionFree.root_injective source B hSourceScope hB
      entry X (Or.inl hEntrySource) (Or.inr hXB) hEntryRoot
  have hPB : NamedBlock.Preceq P B := by
    rw [hEntryEq] at hPEntry
    exact named_trans hPEntry hXB
  have hCompatible : NamedBlock.compatible P B = true := by
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    exact Or.inl hPB
  exact Bool.false_ne_true (hConflict.symm.trans hCompatible)

end DecoupledConsensusModel.Proofs.NamedConflictingCarrierBand

end
