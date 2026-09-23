module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.HeightRegimeNamed
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryBoundaryNamed

@[expose] public section

/-!
# Named nonjustifiable height-regime base

The recovery-height case uses the existing raw recovery frame for the local FG
root calculation. Its predecessor and all public block witnesses remain named.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem namedGenesis_preceq (B : NamedBlock V) :
    NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => rfl
  | node parent slot root votes support rows proposer ih =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer ih

private theorem namedGenesis_runBlock
    (S : Setup V) {rho : Run V} (hbelow : BelowOneThird S rho.honest) :
    RunBlock S rho (NamedBlock.genesis : NamedBlock V) := by
  obtain ⟨v, hv⟩ : rho.honest.Nonempty := by
    by_contra hempty
    have hm := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
    simpa [HonestWeightMajority, Finset.not_nonempty_iff_eq_empty.mp hempty,
      Electorate.weightOf] using hm
  refine ⟨NamedBlock.genesis, Or.inr ⟨v, hv, 0, ?_⟩,
    Proofs.NamedAncestry.named_self NamedBlock.genesis⟩
  change (NamedBlock.genesis : NamedBlock V) ∈
    ({NamedBlock.genesis} : Finset (NamedBlock V))
  exact Finset.mem_singleton_self _

/-- The named recovery frame is the established raw recovery frame with a
named genesis predecessor. -/
theorem namedHeightRegimeFrame_of_recovery
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (c0 : Round) :
    NamedHeightRegimeFrame S rho blocked stop NamedBlock.genesis c0 := by
  have hraw := heightRegimeFrame_of_recovery
    S adm hbelow hcap hrec hfrontier
  refine ⟨?_, namedGenesis_runBlock S hbelow, ?_, ?_, ?_⟩
  · intro v hv n hn X hXrun hXheight hgenX
    exact hraw.floor v hv n hn X hXrun hXheight
      (Protocol.preceq_genesis X.erase)
  · change 1 ≤ blocked
    exact Nat.succ_le_of_lt
      ((Nat.zero_le (hF0 + 1)).trans_lt (NjGap.lt_of_recoveryHeight hrec))
  · intro v hv n hn Q hQmem hQheight hgenQ
    have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
    have hQraw : Q.erase ∈ (rho.stateBefore S n v).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hQmem
    have hview := Proofs.NamedStoreBridge.derivedView_stateBefore S rho n v Q hQmem
    have hQstored :
        ((rho.stateBefore S n v).st.core.σ Q.erase).h = blocked + 1 := by
      rw [hview, hQheight]
    exact hraw.rootBelow v hv n hn Q.erase hQraw hQstored
      (Protocol.preceq_genesis Q.erase)
  · intro p hp r hr hhor B hBmem hsource hBheight
    exact namedGenesis_preceq B

/-- The nonjustifiable height is a named base. The previous checkpoint is the
named genesis block. -/
theorem namedHeightRegimeBase_of_recovery
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} {first : Nat} {blocked hF0 : Height}
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hstart : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < blocked) :
    NamedHeightRegimeBase S rho r0 blocked first NamedBlock.genesis := by
  refine ⟨hfirst, hstart, ?_, ?_, ?_⟩
  · exact Nat.succ_le_of_lt
      ((Nat.zero_le (hF0 + 1)).trans_lt (NjGap.lt_of_recoveryHeight hrec))
  · intro c hminimal
    exact namedHeightRegimeFrame_of_recovery S adm hbelow
      (honestPrefixFinalityCap_of_le S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Nat.sub_le first 1) hcap)
      hrec
      (Nat.lt_succ_of_le
        (hfirst.before _ (Nat.sub_lt hfirst.positive Nat.one_pos))) c
  · intro a ta ha hemit hbefore R hRh hpair hR w hw time hfrontier hroot
      X hXrun hXh hprev
    exact False.elim ((honestEmittedTarget_height_ne_recovery_named
      S adm hcap hrec ha hemit hbefore.le hpair) rfl)

#print axioms namedHeightRegimeFrame_of_recovery
#print axioms namedHeightRegimeBase_of_recovery

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
