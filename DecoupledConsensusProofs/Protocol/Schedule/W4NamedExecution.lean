module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedFoldIteration
public import DecoupledConsensusProofs.Protocol.Schedule.W4BaseFold
public import DecoupledConsensusProofs.Execution.W4IteratePinFree
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecState
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierRecord

@[expose] public section

/-! # Named complete state and execution from the handoff triple
This leaf is above the fold producers and the compatibility execution interface. It
copies the two assemblers at their consumer-facing shapes, replacing the
compatibility row-cap boundary by `W4NamedHandoffBoundaryCore`. The prepared
execution record keeps its `actionHeadAt` field; the false universal
`W4OpeningHeadReadPin` is not used.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}




private theorem w4nex_two_succ_shift (o n : Nat) :
    o + 2 + n + 1 = o + 3 + n := by
  omega






/-- The selected-round form of the named fold producer. It retains the
initial fold and the late-round guard as inputs, then uses the hybrid
iterator's separate ceiling and ordinary supply routes. -/
theorem w4NamedFoldAtEverySlotFrom_of_initial
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    {F0 : Slot → Block V} {End0 : Block V}
    (hfold0 : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) (S.hc.opening_slot q + 3) F0 End0)
    (hbaseEq0 : F0 (S.hc.opening_slot q + 3) = D.erase) :
    ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ F : Slot → Block V, ∃ End : Block V,
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase := by
  have hcarrierBase := hboundary.carrierCeiling
  have hcarrierQ := w4CarrierCeilingAtQPin_of_prepared S adm hfb
    q D carrier hhandoff hbaseTiming hcarrierBase
  have hdeadline : ∀ {j : Slot},
      S.hc.opening_slot q + 3 ≤ j + 1 →
      S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ j + 2 := by
    intro j hj
    have hround : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
      (Nat.le_succ _).trans hqLate
    have hopen : S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
        S.hc.opening_slot q :=
      Nat.mul_le_mul_right S.hc.R hround
    have hqj : S.hc.opening_slot q ≤ j + 2 := by
      exact (Nat.le_add_right (S.hc.opening_slot q) 3).trans
        (hj.trans (Nat.le_succ _))
    exact hopen.trans hqj
  intro s hs hhor
  let n : Nat := s - (S.hc.opening_slot q + 3)
  have htarget : S.hc.opening_slot q + 3 + n = s := by
    dsimp only [n]
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hs
  have hcnSucc : S.hc.opening_slot q + 2 + n + 1 = s := by
    calc
      S.hc.opening_slot q + 2 + n + 1 =
          S.hc.opening_slot q + 3 + n := by
            exact w4nex_two_succ_shift _ _
      _ = s := htarget
  have hsPos : 0 < s :=
    Nat.lt_of_lt_of_le (Nat.succ_pos _) hs
  have hcn : S.hc.opening_slot q + 2 + n = s - 1 := by
    apply Nat.succ.inj
    exact hcnSucc.trans (Nat.succ_pred_eq_of_pos hsPos).symm
  have hhorIter : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 2 + n) ≤ rho.horizon := by
    simpa only [hcn] using hhor
  obtain ⟨F, End, hfold, hbaseEq⟩ :=
    w4MovingSlotFoldAtN_iterate_hybrid_named S adm hcom hfb hrec hdelay
      hpost (q := q) (D := D) (M0 := M0) hbaseTiming.1
      hbaseTiming.2.1 hcarrierBase hcarrierQ
      (c := S.hc.opening_slot q + 2) (F := F0) (End := End0) hfold0
      (hsBase := by
        show S.hc.opening_slot q + 3 ≤
          (S.hc.opening_slot q + 2) + 1
        exact Nat.le_refl _)
      (hbaseEq := hbaseEq0) (hdeadline := hdeadline) n hhorIter
  rw [show (S.hc.opening_slot q + 2) + 1 =
      S.hc.opening_slot q + 3 by rfl, htarget] at hfold
  exact ⟨F, End, hfold, hbaseEq⟩

#print axioms w4NamedFoldAtEverySlotFrom_of_initial













end HealingSurface
end Proofs
end DecoupledConsensusModel

end
