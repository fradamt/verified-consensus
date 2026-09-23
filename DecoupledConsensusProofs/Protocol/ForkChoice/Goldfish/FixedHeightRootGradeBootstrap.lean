module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers

@[expose] public section

/-! # Fixed-height root-floor grade bootstrap
A fixed-height root interference either raises the public honest frontier by a
bounded endpoint, or gives a later recurrent carrier whose preceding action
has the previous root as its exact FG-root floor. The following strict action read
keeps that root active, so the standard grade bootstrap forms the next common
G2.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A bounded proposer recurrence turns a fixed-height justification root into
one named common grade at the previous target, unless the public frontier rises. -/
theorem fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {r gap : Round}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ S.a r)
    (hrecurrence : MultiProposerRecurrence S rho gap)
    (hendHor : S.a (r + 4 + gap) ≤ rho.horizon) :
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∃ q : Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          ProposerCarrierAt S rho q ∧
            NamedGradeFormsAt S rho (q - 1)
              (rho.storeBeforeTime S w read).J := by
  by_cases hrise : H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  · right
    have hcapEnd : honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H :=
      Nat.le_of_not_gt hrise
    obtain ⟨q, hqlo, hqhi, hcarrier⟩ := hrecurrence (r + 3)
    have hqlo' : r + 1 + 2 ≤ q := by
      simpa only [Nat.add_assoc] using hqlo
    have hqTwo : 2 ≤ q :=
      (Nat.le_add_left 2 (r + 1)).trans hqlo'
    have hqActionLower : r + 1 ≤ q - 2 :=
      Nat.le_sub_of_add_le hqlo'
    have hqActionBase : r ≤ q - 2 :=
      (Nat.le_succ r).trans hqActionLower
    have hqActionSucc : q - 2 ≤ q - 1 :=
      Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
    have hbaseEnd : r + 3 ≤ r + 4 :=
      Nat.add_le_add_left (Nat.le_succ 3) r
    have hqEnd : q ≤ r + 4 + gap :=
      hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
    have hqActionEnd : q - 2 ≤ r + 4 + gap :=
      (Nat.sub_le q 2).trans hqEnd
    have hqNextEnd : q - 1 ≤ r + 4 + gap :=
      (Nat.sub_le q 1).trans hqEnd
    have hqPred : q - 2 + 1 = q - 1 := by
      have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
      rw [← hqEq]
      simp
    have hactionMono : S.a r ≤ S.a (q - 2) :=
      Assembly.a_mono S hqActionBase
    have hreadActionAt : read ≤ S.a (q - 2) :=
      hreadAction.trans hactionMono
    have hdelayAction : read + S.E.Δ ≤ S.a (q - 2) := by
      calc
        read + S.E.Δ ≤ S.a r + S.E.Δ :=
          Int.add_le_add_right hreadAction S.E.Δ
        _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
          action_add_delta_le_next_Γ_neg1 S r
        _ ≤ S.a (r + 1) :=
          le_of_lt (next_Γ_neg1_lt_action S r)
        _ ≤ S.a (q - 2) := Assembly.a_mono S hqActionLower
    have hpostAction : S.E.t_GST ≤ S.a (q - 2) :=
      hpost.trans hreadActionAt
    have hactionEnd : S.a (q - 2) ≤ S.a (r + 4 + gap) :=
      Assembly.a_mono S hqActionEnd
    have hactionHor : S.a (q - 2) ≤ rho.horizon :=
      hactionEnd.trans hendHor
    have hcapAction : honestHMaxAt S rho (S.a (q - 2)) ≤ H :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hactionEnd).trans hcapEnd
    have hnextEnd : S.a (q - 1) ≤ S.a (r + 4 + gap) :=
      Assembly.a_mono S hqNextEnd
    have hnextHor : S.a (q - 1) ≤ rho.horizon :=
      hnextEnd.trans hendHor
    have hcapNext : honestHMaxAt S rho (S.a (q - 1)) ≤ H :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hnextEnd).trans hcapEnd
    have hdelayNext : read + S.E.Δ ≤ S.a (q - 1) :=
      hdelayAction.trans (Assembly.a_mono S hqActionSucc)
    have hcut : S.hc.Γ_neg1 S.E.Δ (q - 1) ≤ rho.horizon := by
      have hcutAction : S.hc.Γ_neg1 S.E.Δ (q - 1) ≤ S.a (q - 1) := by
        simpa only [hqPred] using
          (le_of_lt (next_Γ_neg1_lt_action S (q - 2)))
      exact hcutAction.trans hnextHor
    have hsb : SlashableBound S rho :=
      slashableBound_of_admissible_belowOneThird S adm hfb
    have hrootEq {p : V} (hp : p ∈ rho.honest) {target : Time}
        (hdelay : read + S.E.Δ ≤ target)
        (hhor : target ≤ rho.horizon)
        (hcap : honestHMaxAt S rho target ≤ H) :
        Protocol.get_fg_root
            (rho.storeBeforeTime S p target).toHealing.toFG =
          (rho.storeBeforeTime S w read).J := by
      have hlocalCap : (rho.storeBeforeTime S p target).h_max ≤ H :=
        ((storeBeforeTime_hMax_le_storeAt
          S adm.toNamedScheduleWellFormed p target).trans
          (localHMax_le_honestHMaxAt S rho target hp)).trans hcap
      obtain ⟨carrier, hcarrierAt, _hcarrierRun, hcarrierJust,
          hcarrierTarget⟩ :=
        fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRise
          S adm hsb h hp hpost hdelay hhor hcap
      exact
        fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_le
          S adm h hp hcarrierAt hcarrierJust hcarrierTarget hlocalCap
    have hfloor : ∀ v ∈ rho.honest,
        Block.Preceq (rho.storeBeforeTime S w read).J
          (Protocol.get_fg_root
            (actionStoreAt S rho v (q - 2)).toHealing.toFG) := by
      intro v hv
      have hroot := hrootEq hv hdelayAction hactionHor hcapAction
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v (q - 2), hroot]
      exact Block.preceq_self _
    have hactiveNext : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S w read).J ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v (q - 1)).toFG := by
      intro v hv
      change (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S v (S.a (q - 1))).toHealing.toFG
      have hroot := hrootEq hv hdelayNext hnextHor hcapNext
      rw [← hroot]
      simpa only [Run.storeBeforeTime] using
        named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a (q - 1)) v
    let domainRead := DecoupledConsensusModel.Protocol.domain S.E S.hc (q - 1) .g2
    have hdomainAction : domainRead ≤ S.a (q - 1) := by
      exact FrameForward.domain_le_a S (q - 1) .g2
    have hdomainEnd : domainRead ≤ S.a (r + 4 + gap) :=
      hdomainAction.trans hnextEnd
    have hdomainHor : domainRead ≤ rho.horizon :=
      hdomainEnd.trans hendHor
    have hdomainCap : honestHMaxAt S rho domainRead ≤ H :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hdomainEnd).trans hcapEnd
    have hdelayDomain : read + S.E.Δ ≤ domainRead := by
      have hnext := action_add_delta_le_next_Γ_neg1 S (q - 2)
      rw [gammaNeg1_eq_domain_g2_succ S (q - 2)] at hnext
      exact hdelayAction.trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (by simpa only [domainRead, hqPred] using hnext))
    have hactiveDomain : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S w read).J ∈
          PhaseGrades.filteredTree (relativeG2Read S rho (q - 1) v) := by
      intro v hv
      have hroot := hrootEq hv hdelayDomain hdomainHor hdomainCap
      change (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S v domainRead).toHealing.toFG
      rw [← hroot]
      simpa only [Run.storeBeforeTime] using
        named_fgRoot_mem_filtered_stateBeforeTime S rho domainRead v
    have hcutRaw : S.hc.Γ_neg1 S.E.Δ ((q - 2) + 1) ≤ rho.horizon := by
      simpa only [hqPred] using hcut
    have hactiveRaw : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S w read).J ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v ((q - 2) + 1)).toFG := by
      simpa only [hqPred] using hactiveNext
    have hactiveDomainRaw : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S w read).J ∈
          PhaseGrades.filteredTree (relativeG2Read S rho ((q - 2) + 1) v) := by
      simpa only [hqPred] using hactiveDomain
    have hmajority : HonestWeightMajority S rho.honest :=
      AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
        (S := S) hfb
    have hformsRaw := namedGradeFormsAt_succ_of_fgRootFloor
      (P := (rho.storeBeforeTime S w read).J)
      (F := (rho.storeBeforeTime S w read).J)
      S adm hmajority hfloor hpostAction hcutRaw hactiveRaw hactiveDomainRaw
    exact ⟨q, hqlo, hqhi, hcarrier,
      by simpa only [hqPred] using hformsRaw⟩

#print axioms
  fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBound



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
