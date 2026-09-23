module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical

@[expose] public section

/-!
# SG safety across a fixed gate-off window

This exports the safety content used inside height progress. It retains the
exact old SG target across every later covered round. The common-frontier
window remains explicit; it is not the final post-recovery safety theorem.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every honest round-`c` SG target stays below all honest Goldfish votes in
later covered rounds of a fixed gate-off window. No proposer recurrence or
height-progress conclusion is needed. -/
theorem sgVotesCone_laterRounds_of_gateOffWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hfb : BelowOneThird S rho.honest)
    {M : Height} {c last : Round} (hc : 1 ≤ c) (hlast : c + 1 ≤ last)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (last + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (last + 2))
    (hready : GradeRoundReady S rho c) :
    ∀ v ∈ rho.honest, ∀ k : Round, c + 1 ≤ k → k ≤ last →
      ∀ s : Slot, S.hc.opening_slot k ≤ s → s ≤ seedRoundLastSlot S k →
        NamedHonestVotesCone S rho s
          (fun X => Block.Preceq (actionSGBlockAt S rho v c) X) := by
  have hhorBase : S.a (c + 2) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.add_le_add_right (Nat.le_of_succ_le hlast) 2)).trans hhor
  have hframeBase : GateOffFrameAt S rho M (c - 1) (c + 2) := by
    intro read hlo hhi w hw
    exact hframe read hlo
      (hhi.trans (Assembly.a_mono S
        (Nat.add_le_add_right (Nat.le_of_succ_le hlast) 2))) w hw
  have hdis := seedRoundDischarge_of_canonicity S adm hcom hfb hc hpost
    ((Assembly.a_mono S (Nat.le_succ (c + 1))).trans hhorBase)
    (fun read hlo hhi w hw => hframeBase read hlo
      (hhi.trans (Assembly.a_mono S (Nat.le_succ (c + 1)))) w hw)
    hready
  obtain ⟨_, C, hC⟩ := seedBoundaryAdoption_of_discharge
    S adm hcom hfb hc hpost hhorBase hframeBase hdis
  have hregime : ∀ k : Round, c + 1 ≤ k → k < last →
      RoundCeilingNextRegimeAt S rho M k := by
    intro k hklo hkhi
    have hpred : c - 1 ≤ k :=
      (Nat.sub_le c 1).trans ((Nat.le_succ c).trans hklo)
    have hnext : k + 2 ≤ last + 2 := Nat.add_le_add_right (Nat.le_of_lt hkhi) 2
    apply regime_of_gateOffFrame S adm hfb
      (hpost.trans (Assembly.a_mono S hpred))
      ((Assembly.a_mono S hnext).trans hhor)
    intro read hlo hhi w hw
    exact hframe read ((Assembly.a_mono S hpred).trans hlo)
      (hhi.trans (Assembly.a_mono S hnext)) w hw
  intro v hv k hklo hkhi s hslo hshi
  obtain ⟨Ck, hCk, hCCk⟩ :=
    roundCeiling_through_or_rebase S adm hcom hfb hC hregime k hklo hkhi
  have hBC : Block.Preceq (actionSGBlockAt S rho v c) C.erase := by
    simpa only [Nat.add_sub_cancel] using hC.previousCarriers v hv
  have hcone := roundCeiling_votesThrough S adm hcom hCk s hslo hshi
  intro w hw hwCommittee
  obtain ⟨X, hCX, hXrun, hXemit⟩ := hcone w hw hwCommittee
  exact ⟨X, Block.preceq_trans hBC (Block.preceq_trans hCCk hCX), hXrun, hXemit⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
