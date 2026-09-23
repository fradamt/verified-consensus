module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.SafetyCompatibilityJoin
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationAdoption
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapSlot
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction

@[expose] public section

/-!
# Finite SG participation windows

Only the last source action in the SG window must be inside the run.
The next action can be outside the horizon of a vote read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem previousRound_mem_latestWindow {eta r : Nat}
    (heta : 1 ≤ eta) (hr : 0 < r) : r - 1 ∈ Protocol.latest_window eta r := by
  simp only [Protocol.latest_window, List.mem_range']
  refine ⟨min eta r - 1, by omega, ?_⟩
  simp only [one_mul]
  omega

/-- The last SG source action precedes its vote read. -/
theorem windowSourceTime_le_vote (S : Setup V) {s : Slot}
    (hr : 0 < S.hc.round_of s) :
    S.a (S.hc.round_of s - 1) ≤ Protocol.vote_time S.E s :=
  (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
    (WeakSG.window_deadline_le_vote S (previousRound_mem_latestWindow S.hc.η_SG_ge_one hr))

/-- The last source action precedes every vote at or after its window's opening. -/
theorem windowSourceTime_le_vote_of_opening_le (S : Setup V) {r : Round} {s : Slot}
    (hr : 0 < r) (hopen : S.hc.opening_slot r ≤ s) :
    S.a (r - 1) ≤ Protocol.vote_time S.E s := by
  have htime := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S
    (Nat.sub_lt hr (by decide : 0 < (1 : Nat)))
  have hvote : Protocol.proposal_time S.E s ≤ Protocol.vote_time S.E s := by
    change S.E.t s ≤ S.E.t s + S.E.Δ
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  exact (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
    ((htime.trans (proposal_time_mono S.E hopen)).trans hvote)

/-- A finite destination supplies the window needed for the weight comparison. -/
theorem honestWeightMajority_of_finiteWindowsFrom (S : Setup V) {rho : Run V}
    {cut : Round} {d last : Slot}
    (hawake : ∀ r, cut ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    (hcut : 0 < cut) (hopen : S.hc.opening_slot cut ≤ d)
    (hupper : d ≤ last + 1)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon) :
    HonestWeightMajority S rho.honest := by
  have hvoteHor : Protocol.vote_time S.E (last + 1) ≤ rho.horizon := by
    apply le_trans ?_ hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E last]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  exact WeakSG.honestWeightMajority_of_awakeWindowMajority S
    (hawake cut (Nat.le_refl _) ((windowSourceTime_le_vote_of_opening_le S hcut hopen).trans
      ((vote_time_mono_slots S.E hupper).trans hvoteHor)))


namespace WeakGenesis

/-- A relevant positive window supplies the global weight comparison. -/
theorem honestWeightMajority_of_finiteWindows (S : Setup V) {rho : Run V}
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    {last : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon) :
    HonestWeightMajority S rho.honest := by
  have hzero : S.a 0 ≤ rho.horizon := by
    change Protocol.confirmation_time S.E (S.hc.opening_slot 0) ≤ rho.horizon
    simp only [Protocol.HealConfig.opening_slot, Nat.zero_mul]
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.succ_le_succ (Nat.zero_le last))
  exact WeakSG.honestWeightMajority_of_awakeWindowMajority S
    (hawake 1 (by decide) (by simpa using hzero))





#print axioms windowSourceTime_le_vote
#print axioms windowSourceTime_le_vote_of_opening_le
#print axioms honestWeightMajority_of_finiteWindowsFrom
#print axioms honestWeightMajority_of_finiteWindows


/-
/-- Every genuine confirmation stays below later honest Goldfish votes from GST zero. -/
theorem protectedVoteSlots_of_gstZero_finiteWindows (S: Setup V) {rho: Run V}
    (adm: AdmissibleCore S rho) (hcom: HonestCommittees S rho.honest)
    (hgst: S.E.t_GST = 0)
    (hawake: ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon → AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    {last: Slot} (hhor: Protocol.confirmation_time S.E last ≤ rho.horizon):
    ∀ d, 1 ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B):= by
  have hzero: S.a 0 ≤ rho.horizon:= by
    change Protocol.confirmation_time S.E (S.hc.opening_slot 0) ≤ rho.horizon
    simp only [Protocol.HealConfig.opening_slot, Nat.zero_mul]
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.succ_le_succ (Nat.zero_le last))
  have hmajority:= WeakSG.honestWeightMajority_of_awakeWindowMajority S
    (hawake 1 (by decide) (by simpa using hzero))
  have hvoteHor: Protocol.vote_time S.E (last + 1) ≤ rho.horizon:= by
    apply le_trans ?_ hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E last]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hseed:= protectedVoteSlot_genesis S adm (by decide: 0 < (1: Slot))
    ((vote_time_mono_slots S.E (Nat.succ_le_succ (Nat.zero_le last))).trans hvoteHor)
  have hpost: S.E.t_GST ≤ Protocol.proposal_time S.E 1:= by
    rw [hgst]
    exact proposal_time_nonneg S.E 1
  have hwindowPost (r: Round): S.E.t_GST ≤ S.a (r - S.hc.η_SG):= by
    rw [hgst]
    exact Proofs.HealingLemmas.a_nonneg S _
  have hfold:= WeakJoint.protectedVoteSlots_of_historyCut S adm hcom hmajority
    (base:= 0) (cut:= 0) (start:= 1) (last:= last)
    (Nat.zero_le _) (by decide) (by simp [Protocol.HealConfig.opening_slot])
    hpost hhor hseed
  have hresult:= hfold ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro d hd hu
    obtain ⟨hgen, hconfs⟩:= hresult d hd hu
    exact ⟨hgen, fun q hq w hw B hB => hconfs q (by simp [Protocol.HealConfig.opening_slot])
      hq w hw B hB⟩
  · intro e he hu B hPB w hw hhigh a ta T ha hemit htime hheight hold
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro r hr hold
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro q hq hqone w hw B hB
    have hqzero: q = 0:= Nat.lt_one_iff.mp hqone
    subst q
    rw [genuineConfirmation_zero_eq_genesis S adm hmajority hw hB]
    exact Block.preceq_self _
  · intro r hr ht w hw a
    dsimp only
    intro ha hemit hold
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro d hd hu w hw a ta
    dsimp only
    intro ha hemit ht hold
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro r hr hrpos ht w hw _
    exact sgWindowMajority_of_windowHonestMajorityAt S.E
      (WeakSG.windowHonestMajorityAt_action S adm hw (hawake r hrpos ((Assembly.a_mono S (Nat.sub_le r 1)).trans (ht.le.trans hvoteHor)))
        (hwindowPost r) (ht.le.trans hvoteHor))
  · intro d hd hu hrpos w hw
    exact sgWindowMajority_of_windowHonestMajorityAt S.E
      (WeakSG.windowHonestMajorityAt_voteDuty S adm hw (hawake _ hrpos (windowSourceTime_le_vote S hrpos |>.trans ((vote_time_mono_slots S.E hu).trans hvoteHor)))
        (hwindowPost _) ((vote_time_mono_slots S.E hu).trans hvoteHor))

/-- The finite all-awake instance has no finality-source residual. -/
theorem protectedVoteSlots_of_gstZero_allAwake (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hcom: HonestCommittees S rho.honest)
    (hgst: S.E.t_GST = 0) (hmajority: HonestWeightMajority S rho.honest)
    {last: Slot} (hhor: Protocol.confirmation_time S.E last ≤ rho.horizon):
    ∀ d, 1 ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B):=
  protectedVoteSlots_of_gstZero_finiteWindows S adm.toAdmissibleCore hcom hgst
    (fun _ hr ht => awakeWindowMajority_of_allAwake S adm hmajority hr ht) hhor

 -/

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
