module
public import DecoupledConsensusInternal.ModelVocabulary
public import Mathlib
public import DecoupledConsensusInternal.Legacy.Interface
public import DecoupledConsensusInternal.Legacy.Definitions.Confirmation
public import DecoupledConsensusStatements.Instantiation.Deadlines
public import DecoupledConsensusInternal.Legacy.Definitions.NamedEvidenceInternal
public import DecoupledConsensusInternal.Legacy.Definitions.NamedOutageEntry
public import DecoupledConsensusInternal.Legacy.Definitions.ProposalSourcesInternal
public import DecoupledConsensusStatements.Instantiation.RoundTimes
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # The protocol instance of the public interface

This file is the small audit bridge from protocol definitions to the generic
statement vocabulary. Every field is a closed existing protocol definition.
-/

namespace DecoupledConsensusModel
namespace Statements

open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem roundPeriod_time_pos (S : Setup V) :
    0 < S.a 1 - S.a 0 := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  have hR : (0 : Int) < (S.hc.R : Int) := by
    have hR3 : (3 : Int) ≤ (S.hc.R : Int) := by
      exact_mod_cast S.hc.R_ge_three
    omega
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hp : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by
    positivity
  simpa using hp

private theorem roundPeriod_pos (S : Setup V) :
    0 < roundPeriod S := by
  unfold roundPeriod
  have hne : Int.toNat (S.a 1 - S.a 0) ≠ 0 := by
    intro hz
    have hzle : S.a 1 - S.a 0 ≤ 0 := Int.toNat_eq_zero.mp hz
    exact (not_le_of_gt (roundPeriod_time_pos S)) hzle
  exact Nat.pos_of_ne_zero hne

private theorem action_time_formula (S : Setup V) (r : Round) :
    S.a r = S.a 0 + (r : Time) * (S.a 1 - S.a 0) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  ring

private theorem ceil_bound {d L : Nat} (hL : 0 < L) :
    d ≤ L * (d ⌈/⌉ L) := by
  simpa [nsmul_eq_mul] using
    (le_smul_ceilDiv (α := Nat) (β := Nat) hL)

theorem roundAt_spec (S : Setup V) (t : Time) :
    t ≤ S.a (roundAt S t) := by
  by_cases h : 0 ≤ t - S.a 0
  · let d : Nat := Int.toNat (t - S.a 0)
    let L : Nat := roundPeriod S
    have hd : (d : Time) = t - S.a 0 := by
      dsimp [d]
      exact Int.toNat_of_nonneg h
    have hL : 0 < L := roundPeriod_pos S
    have hLtime : (L : Time) = S.a 1 - S.a 0 := by
      dsimp [L, roundPeriod]
      exact Int.toNat_of_nonneg (roundPeriod_time_pos S).le
    have hceil := ceil_bound (d := d) (L := L) hL
    have hceilInt : (d : Time) ≤ (L : Time) * ((d ⌈/⌉ L : Nat) : Time) := by
      exact_mod_cast hceil
    have hdiff : t - S.a 0 ≤
        (L : Time) * ((d ⌈/⌉ L : Nat) : Time) := by
      rw [← hd]
      exact hceilInt
    calc
      t = S.a 0 + (t - S.a 0) := by ring
      _ ≤ S.a 0 + (L : Time) * ((d ⌈/⌉ L : Nat) : Time) :=
        Int.add_le_add_left hdiff _
      _ = S.a 0 + ((d ⌈/⌉ L : Nat) : Time) * (S.a 1 - S.a 0) := by
        rw [hLtime]
        ring
      _ = S.a (roundAt S t) := by
        rw [action_time_formula S (roundAt S t)]
        rfl
  · have ht : t ≤ S.a 0 := le_of_lt (sub_neg.mp (lt_of_not_ge h))
    have hd0 : Int.toNat (t - S.a 0) = 0 :=
      Int.toNat_eq_zero.mpr (sub_nonpos.mpr ht)
    have hq0 : roundAt S t = 0 := by
      simp [roundAt, nextRound, hd0]
    rw [hq0]
    exact ht

theorem roundAt_min (S : Setup V) (t : Time) {r : Round}
    (hr : r < roundAt S t) : ¬ t ≤ S.a r := by
  by_cases h : 0 ≤ t - S.a 0
  · let d : Nat := Int.toNat (t - S.a 0)
    let L : Nat := roundPeriod S
    have hd : (d : Time) = t - S.a 0 := by
      dsimp [d]
      exact Int.toNat_of_nonneg h
    have hL : 0 < L := roundPeriod_pos S
    have hLtime : (L : Time) = S.a 1 - S.a 0 := by
      dsimp [L, roundPeriod]
      exact Int.toNat_of_nonneg (roundPeriod_time_pos S).le
    have hnot : ¬ d ≤ L * r := by
      intro hdr
      have hqle : d ⌈/⌉ L ≤ r := (ceilDiv_le_iff_le_mul hL).2 hdr
      exact (Nat.not_lt_of_ge hqle)
        (by simpa [roundAt, nextRound, d, L] using hr)
    have hlt : L * r < d := Nat.lt_of_not_ge hnot
    have hltInt : (L : Time) * (r : Time) < (d : Time) := by
      exact_mod_cast hlt
    have hltTime : (r : Time) * (S.a 1 - S.a 0) < t - S.a 0 := by
      rw [← hLtime, ← hd]
      simpa [mul_comm] using hltInt
    intro htr
    rw [action_time_formula S r] at htr
    have hltAbs : S.a 0 + (r : Time) * (S.a 1 - S.a 0) < t := by
      have hlt' := (lt_sub_iff_add_lt).mp hltTime
      simpa [add_comm] using hlt'
    exact (not_lt_of_ge htr) hltAbs
  · have ht : t ≤ S.a 0 := le_of_lt (sub_neg.mp (lt_of_not_ge h))
    have hd0 : Int.toNat (t - S.a 0) = 0 :=
      Int.toNat_eq_zero.mpr (sub_nonpos.mpr ht)
    have hq0 : roundAt S t = 0 := by
      simp [roundAt, nextRound, hd0]
    exfalso
    exact (Nat.not_lt_of_ge (Nat.zero_le r))
      (by simpa [hq0] using hr)

/-- The closed protocol instance of the public interface. -/
def «instance» (S : Setup V) : Interface V where
  confirmed := Protocol.get_confirmed
  stable := Protocol.get_stable
  finalized := fun st => st.F
  proposer := S.E.proposer
  proposalTime := Protocol.proposal_time S.E
  proposedBlock := fun rho s => proposedBlockAt S rho s
  committee := fun s => S.E.committee s
  Certificate := NamedBlock V
  finalizes := fun c T => ∃ h, NamedFinalizedAt S.E S.cfg c T h
  collisionFree := fun c c' => RootInjectiveOnAncestors c.erase c'.erase
  evidence := fun c c' =>
    HasSlashableWeightBetween S.E (chain_attestations c.erase) (chain_attestations c'.erase)
  slashable := fun st st' =>
    HasSlashableWeightBetween S.E (store_attestations st) (store_attestations st')
  inRun := fun rho c => RunBlock S rho c

/-- The closed time constants supplied by this protocol. -/
noncomputable def ourConstants (S : Setup V) : Constants where
  roundLength := S.a 1 - S.a 0
  windowRounds := S.hc.η_SG
  prefixEnd := fun t₀ gap extra => S.a (recoveryRound S t₀ gap extra)
  recoveryEnd := fun t₀ gap extra => healingBoundaryTime S (recoveryRound S t₀ gap extra)
  confirmationDelay := 6 * S.E.Δ
  growthDelay := fun gap =>
    (gap + 1 : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ
  stableGrowthDelay := fun gap =>
    (gap + S.hc.η_SG : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ
  finalityStartup := fun gap extra =>
    healingBoundaryTime S (finalityStartup S gap extra + 1) - S.a 0
  finalityDeadline := fun gap extra =>
    healingBoundaryTime S (finalityDeadline S gap extra + 1) - S.a 0 +
      3 * S.E.Δ
  formationMargin := (S.a 1 - S.a 0) + S.E.Δ
  expiry := fun tS =>
    DecoupledConsensusModel.Protocol.early S.E S.hc
      (S.hc.round_of (S.E.slotOf tS) + S.hc.η_SG + 1) .g2

end Statements
end DecoupledConsensusModel

end
