module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Grades.EventualHeightProgress
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Canonical height density and recurring-finality source height

This module isolates the numeric consequences of the canonical action history.
The current public `CanonicalSuffixExecution` keeps its proposal-chain suffix
and action-output suffix as separate witnesses. The named residual below is
the missing bridge: it states the one-round crossing charge and the relayed
frontier floor. All carrier ordering and nonjustifiability arithmetic after
that bridge are proved here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Total named proposal choice -/

noncomputable def canonicalProposal (S : Setup V) (rho : Run V) (s : Slot) :
    NamedBlock V :=
  Classical.choose (proposedBlockAt_isSome S rho s)

theorem canonicalProposal_spec (S : Setup V) (rho : Run V) (s : Slot) :
    proposedBlockAt S rho s = some (canonicalProposal S rho s) :=
  Classical.choose_spec (proposedBlockAt_isSome S rho s)

/- The round-indexed height API is retained. Its chosen block is the unique
   total named proposal supplied by `canonicalProposal_spec`. -/
/-- Derived height of the exact opening proposal of round `r`. -/
noncomputable def carrierOpeningHeight (S : Setup V) (rho : Run V) (r : Round) : Height :=
  (Protocol.derive_named S.E S.cfg
    (canonicalProposal S rho (S.hc.opening_slot r))).h


/- Open. `CanonicalSuffixExecution` exposes a monotone proposal suffix
and a monotone action-output suffix, but no public field connects the latter
to the next opening proposal. The first field below is the local
crossing-to-action-round charge. The second is the frontier-carrier relay
followed by the parent-keyed `h_max - 1` head floor. -/


























private theorem openingSlot_pos_of_afterBoundary
    (S : Setup V) {q r : Round}
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r)) :
    0 < S.hc.opening_slot r := by
  by_contra hnot
  have heq : S.hc.opening_slot r = 0 := Nat.eq_zero_of_not_pos hnot
  have hproposalBoundary : Protocol.proposal_time S.E
      (S.hc.opening_slot r) < healingBoundaryTime S q := by
    rw [heq]
    unfold healingBoundaryTime
    exact lt_of_lt_of_le (proposal_time_lt_vote_time S.E 0)
      (vote_time_mono_slots S.E (Nat.zero_le _))
  exact (lt_asymm hafter) hproposalBoundary



/-- Two distinct multiples of `K` cannot lie in one open interval of width
`K`. -/
private theorem not_dvd_of_dvd_of_strict_band
    {K H1 H2 : Nat} (hdvd : K ∣ H1) (hstrict : H1 < H2)
    (hband : H2 < H1 + K) : ¬ K ∣ H2 := by
  intro hdvd2
  have hdiffPos : 0 < H2 - H1 := Nat.sub_pos_of_lt hstrict
  have hdvdDiff : K ∣ H2 - H1 := Nat.dvd_sub hdvd2 hdvd
  have hKle : K ≤ H2 - H1 := Nat.le_of_dvd hdiffPos hdvdDiff
  have hdiffLt : H2 - H1 < K := by omega
  exact (Nat.not_lt_of_ge hKle) hdiffLt


theorem named_derive_nj_eq_false_left_or_right_of_strict_band
    (E : Env V) (cfg : Protocol.HeightConfig)
    {B1 B2 : NamedBlock V}
    (hstrict : (Protocol.derive_named E cfg B1).h <
      (Protocol.derive_named E cfg B2).h)
    (hband : (Protocol.derive_named E cfg B2).h <
      (Protocol.derive_named E cfg B1).h + cfg.K) :
    (Protocol.derive_named E cfg B1).nj = false ∨
      (Protocol.derive_named E cfg B2).nj = false := by
  by_cases hnj1 : (Protocol.derive_named E cfg B1).nj = false
  · exact Or.inl hnj1
  · have hnj1True : (Protocol.derive_named E cfg B1).nj = true := by
      cases hvalue : (Protocol.derive_named E cfg B1).nj with
      | false => exact False.elim (hnj1 hvalue)
      | true => rfl
    obtain ⟨hF1, -, hentry1⟩ := NjGap.njEntry_derive_named E cfg B1
    have hnon1 : Protocol.nonjustifiable cfg
        (Protocol.derive_named E cfg B1).h hF1 = true := by
      rw [← hentry1]
      exact hnj1True
    have hdvd1 : cfg.K ∣ (Protocol.derive_named E cfg B1).h := by
      simp only [Protocol.nonjustifiable, Bool.and_eq_true,
        decide_eq_true_eq] at hnon1
      exact hnon1.1
    have hnotDvd2 : ¬ cfg.K ∣
        (Protocol.derive_named E cfg B2).h :=
      not_dvd_of_dvd_of_strict_band hdvd1 hstrict hband
    obtain ⟨hF2, -, hentry2⟩ := NjGap.njEntry_derive_named E cfg B2
    apply Or.inr
    rw [hentry2]
    simp only [Protocol.nonjustifiable, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    exact Or.inl hnotDvd2











/-- The carrier opening proposal never exceeds the honest frontier one round
later. -/
theorem carrierOpeningHeight_le_honestHMaxAt_succ
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 a : Round}
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot a))
    (ha : ProposerCarrierAt S rho a)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot a) ≤ rho.horizon) :
    carrierOpeningHeight S rho a ≤ honestHMaxAt S rho (S.a (a + 1)) := by
  have hpos : 0 < S.hc.opening_slot a :=
    openingSlot_pos_of_afterBoundary S hafter
  have hP : proposedBlockAt S rho (S.hc.opening_slot a) = some
      (canonicalProposal S rho (S.hc.opening_slot a)) :=
    canonicalProposal_spec S rho (S.hc.opening_slot a)
  have hlocal := honestProposedBlock_height_le_honestHMaxAt
    S adm hpos ha.1 hhor hP
  have htime : Protocol.proposal_time S.E (S.hc.opening_slot a) ≤
      S.a (a + 1) := by
    have hconf : S.a a = Protocol.confirmation_time S.E
        (S.hc.opening_slot a) := by
      simp only [Setup.a, Protocol.a_eq_confirmation_time]
    calc
      Protocol.proposal_time S.E (S.hc.opening_slot a) ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot a) :=
        proposal_time_le_confirmation_time S.E _
      _ = S.a a := hconf.symm
      _ ≤ S.a (a + 1) := Assembly.a_mono S (Nat.le_succ a)
  exact hlocal.trans
    (honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed htime)


#print axioms canonicalProposal_spec
#print axioms named_derive_nj_eq_false_left_or_right_of_strict_band
#print axioms carrierOpeningHeight_le_honestHMaxAt_succ

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
