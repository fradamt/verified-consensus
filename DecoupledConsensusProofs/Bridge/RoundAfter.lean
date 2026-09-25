module
public import DecoupledConsensusProofs.Bridge.RoundTimes
public import DecoupledConsensusProofs.Protocol.Handlers.StableOutputSeed

@[expose] public section

/-!
# Round-after bridge

Purpose: identify the outage-window ceiling formula with the least action round.
An auditor checks that both closed forms select the same round at every time.

Defines: `roundAfter_eq_nextRound`.
Read after: the round-time bridge and the outage-window action formula.
-/

namespace DecoupledConsensusModel.Proofs

open Execution Statements Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The outage-window round and the public next round agree. -/
theorem roundAfter_eq_nextRound (S : Setup V) (T : Time) :
    Statements.Instantiation.roundAfter S T =
      Statements.Instantiation.nextRound S T := by
  let L : Time := roundLength S
  let x : Time := T - 6 * S.E.Δ + L - 1
  let q : Time := x / L
  have hL : 0 < L := NamedOutageClosure.roundLength_pos S
  have hfloor : q * L ≤ x := Int.ediv_mul_le x (ne_of_gt hL)
  have hupper : T ≤ S.a (roundAfter S T) := by
    simpa only [nextAction] using NamedOutageClosure.le_nextAction S T
  have hmin (r : Round) (hr : r < roundAfter S T) : S.a r < T := by
    change r < q.toNat at hr
    have hqnonneg : 0 ≤ q := by
      by_contra hn
      have hzero : q.toNat = 0 :=
        Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hn))
      simp [hzero] at hr
    have hrcast : (r : Time) + 1 ≤ q := by
      have hnat : r + 1 ≤ q.toNat := Nat.succ_le_iff.mpr hr
      have hcast : (r : Time) + 1 ≤ (q.toNat : Time) := by
        exact_mod_cast hnat
      simpa only [Int.toNat_of_nonneg hqnonneg] using hcast
    have hmul : ((r : Time) + 1) * L ≤ q * L :=
      mul_le_mul_of_nonneg_right hrcast hL.le
    rw [NamedOutageClosure.a_eq_roundLength]
    change 6 * S.E.Δ + L * (r : Time) < T
    dsimp [x] at hfloor
    nlinarith
  apply Nat.le_antisymm
  · by_contra hn
    have hr : nextRound S T < roundAfter S T := Nat.lt_of_not_ge hn
    have hs : T ≤ S.a (nextRound S T) := by
      simpa only [roundAt] using Statements.roundAt_spec S T
    exact (not_lt_of_ge hs) (hmin _ hr)
  · by_contra hn
    have hr : roundAfter S T < nextRound S T := Nat.lt_of_not_ge hn
    have hnot : ¬ T ≤ S.a (roundAfter S T) :=
      Statements.roundAt_min S T (by simpa only [roundAt] using hr)
    exact hnot hupper

end DecoupledConsensusModel.Proofs

end
