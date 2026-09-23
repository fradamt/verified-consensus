module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4DensityStructures

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared density carrier selection

This is the additive prepared-record twin of
`Proofs.HealingSurface.exists_justifiableCarrierPair_afterTwoProgress_with_property`
(`OpeningCarrierSelectionRun.lean:123`). The execution projection uses the
field-level suffix twin from `W4ExecSuffixRun`; the other three density calls
use the verbatim `carrierBand` and `frontierFloor` fields from
`CanonicalCarrierDensityFromPrepared`.

The private arithmetic and timing helpers are copied from
`OpeningCarrierSelectionRun.lean:59-121` and
`CanonicalDensityDischargeRun.lean:945-998`. They are prefixed because the
source helpers are private and are not importable.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4pcs_nat_le_of_le_of_lt {A B C : Nat}
    (h1 : A ≤ B) (h2 : B < C) : A ≤ C := by omega

private theorem w4pcs_nat_q0_succ_lt_carrier
    {q0 start rawLag c1 : Nat}
    (hstart : q0 ≤ start) (hraw : 0 < rawLag)
    (h : start + 2 * rawLag < c1) : q0 + 1 < c1 := by omega

/-- Copied from `OpeningCarrierSelectionRun.lean:59-65`. -/
private theorem w4pcs_openingProposalTime_le_action
    (S : Setup V) (x : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot x) ≤ S.a x := by
  have hconf : S.a x = Protocol.confirmation_time S.E
      (S.hc.opening_slot x) := by
    simp only [Setup.a, Protocol.a_eq_confirmation_time]
  rw [hconf]
  exact proposal_time_le_confirmation_time S.E _

/-- Copied from `OpeningCarrierSelectionRun.lean:67-70`. -/
private theorem w4pcs_openingSlotMono (hc : Protocol.HealConfig)
    {r r' : Round} (hrr : r ≤ r') : hc.opening_slot r ≤ hc.opening_slot r' := by
  simpa only [Protocol.HealConfig.opening_slot] using
    Nat.mul_le_mul_right hc.R hrr

/-- Copied from `OpeningCarrierSelectionRun.lean:72-74`. -/
private theorem w4pcs_nat_carrier_a_bound
    {start rawLag gap a : Nat}
    (h : a ≤ start + 2 * rawLag + 1 + gap) :
    a ≤ start + 4 * rawLag + 3 * gap + 4 := by omega

/-- Copied from `OpeningCarrierSelectionRun.lean:76-82`. -/
private theorem w4pcs_nat_horizon_step
    {start rawLag gap x : Nat}
    (h : x ≤ start + 4 * rawLag + 3 * gap + 4) :
    x ≤ start + 4 * rawLag + 3 * gap + 5 := by omega

private theorem w4pcs_nat_horizon_succ
    {start rawLag gap x : Nat}
    (h : x ≤ start + 4 * rawLag + 3 * gap + 4) :
    x + 1 ≤ start + 4 * rawLag + 3 * gap + 5 := by omega

private theorem w4pcs_nat_zwindow
    {start rawLag gap a : Nat}
    (h : a ≤ start + 2 * rawLag + 1 + gap) :
    a + 1 + 2 * rawLag + 1 + gap + 1 ≤
      start + 4 * rawLag + 3 * gap + 5 := by omega

private theorem w4pcs_nat_q0_le_succ
    {q0 start rawLag a : Nat}
    (hstart : q0 ≤ start) (h : start + 2 * rawLag + 1 ≤ a) :
    q0 ≤ a + 1 := by omega

private theorem w4pcs_nat_q0_le_carrier
    {q0 start rawLag a : Nat}
    (hstart : q0 ≤ start) (h : start + 2 * rawLag + 1 ≤ a) :
    q0 ≤ a := by omega

private theorem w4pcs_nat_a_lt_z {rawLag a z : Nat}
    (h : a + 1 + 2 * rawLag < z) : a < z := by omega

private theorem w4pcs_nat_zgap_bound
    {start rawLag gap a z : Nat}
    (ha : a ≤ start + 2 * rawLag + 1 + gap)
    (hz : z ≤ a + 1 + 2 * rawLag + 1 + gap) :
    z + gap ≤ start + 4 * rawLag + 3 * gap + 4 := by omega

private theorem w4pcs_nat_c1_bound_of_window
    {start rawLag gap a z c1 : Nat}
    (ha : a ≤ start + 2 * rawLag + 1 + gap)
    (hz : z ≤ a + 1 + 2 * rawLag + 1 + gap) (hc1 : c1 < z) :
    c1 ≤ start + 4 * rawLag + 3 * gap + 4 := by omega

private theorem w4pcs_nat_c2_bound_of_window
    {start rawLag gap a z c1 c2 : Nat}
    (ha : a ≤ start + 2 * rawLag + 1 + gap)
    (hz : z ≤ a + 1 + 2 * rawLag + 1 + gap) (hc1 : c1 < z)
    (hnear : c2 ≤ c1 + gap + 1) :
    c2 ≤ start + 4 * rawLag + 3 * gap + 4 := by omega

private theorem w4pcs_nat_c1_above_of_window
    {start rawLag a c1 : Nat}
    (ha : start + 2 * rawLag + 1 ≤ a) (hac1 : a ≤ c1) :
    start + 2 * rawLag < c1 := by omega

private theorem w4pcs_nat_lt_trans_round {a b c : Nat}
    (h1 : a < b) (h2 : b < c) : a < c := by omega

/-- The prepared-record twin of the carrier-pair selection theorem. -/
theorem exists_justifiableCarrierPair_afterTwoProgress_with_property_prepared
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 rawLag gap start : Round}
    (hdensity : CanonicalCarrierDensityFromPrepared S rho q0)
    (hprogress : EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos : 0 < rawLag)
    {P : Round → Prop}
    (hrec : ∀ k : Round, ∃ r : Round, k ≤ r ∧ r ≤ k + gap ∧
      ProposerCarrierAt S rho r ∧ P r)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hstart : q0 ≤ start)
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E
        (S.hc.opening_slot (start + 2 * rawLag + 1)))
    (hhor : S.a (start + 4 * rawLag + 3 * gap + 5) ≤ rho.horizon) :
    ∃ c1 c2 : Round,
      start + 2 * rawLag < c1 ∧ c1 < c2 ∧ c2 ≤ c1 + gap + 1 ∧
        c2 ≤ start + 4 * rawLag + 3 * gap + 4 ∧
        ProposerCarrierAt S rho c1 ∧ ProposerCarrierAt S rho c2 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c1 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c2 ∧
        (∃ P1 P2 : NamedBlock V,
          proposedBlockAt S rho (S.hc.opening_slot c1) = some P1 ∧
          proposedBlockAt S rho (S.hc.opening_slot c2) = some P2 ∧
          ((Protocol.derive_named S.E S.cfg P1).nj = false ∨
            (Protocol.derive_named S.E S.cfg P2).nj = false)) ∧
        P c1 ∧ P c2 := by
  have hplain : MultiProposerRecurrence S rho gap := by
    intro k
    obtain ⟨r, hlo, hhi, hc, _⟩ := hrec k
    exact ⟨r, hlo, hhi, hc⟩
  obtain ⟨a, haLo, haHi, ha, haP⟩ := hrec (start + 2 * rawLag + 1)
  have haBound : a ≤ start + 4 * rawLag + 3 * gap + 4 :=
    w4pcs_nat_carrier_a_bound haHi
  have hafterA : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot a) :=
    hafter.trans_le
      (proposal_time_mono S.E (w4pcs_openingSlotMono S.hc haLo))
  have hstepHor : ∀ x : Round, x ≤ start + 4 * rawLag + 3 * gap + 4 →
      S.a x ≤ rho.horizon := by
    intro x hx
    exact (Assembly.a_mono S (w4pcs_nat_horizon_step hx)).trans hhor
  have hstepHorSucc : ∀ x : Round, x ≤ start + 4 * rawLag + 3 * gap + 4 →
      S.a (x + 1) ≤ rho.horizon := by
    intro x hx
    exact (Assembly.a_mono S (w4pcs_nat_horizon_succ hx)).trans hhor
  have hproposalHor : ∀ x : Round, x ≤ start + 4 * rawLag + 3 * gap + 4 →
      Protocol.proposal_time S.E (S.hc.opening_slot x) ≤ rho.horizon := by
    intro x hx
    exact (w4pcs_openingProposalTime_le_action S x).trans (hstepHor x hx)
  have hzWindowHor : S.a (a + 1 + 2 * rawLag + 1 + gap + 1) ≤
      rho.horizon :=
    (Assembly.a_mono S (w4pcs_nat_zwindow haHi)).trans hhor
  obtain ⟨z, hzLo, hzHi, hz, hzHeight⟩ :=
    carrierOpening_height_gt_of_twoProgress_carrier_of_frontierFloor S adm
      hdensity.frontierFloor hprogress hrawPos hplain
      (w4pcs_nat_q0_le_succ hstart haLo) hzWindowHor
  have haStrict : carrierOpeningHeight S rho a <
      carrierOpeningHeight S rho z :=
    lt_of_le_of_lt
      (carrierOpeningHeight_le_honestHMaxAt_succ S adm hafterA ha
        (hproposalHor a haBound)) hzHeight
  have haz : a < z := w4pcs_nat_a_lt_z hzLo
  have hzgapHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (z + gap)) ≤ rho.horizon :=
    hproposalHor (z + gap) (w4pcs_nat_zgap_bound haHi hzHi)
  obtain ⟨c1, c2, hac1, hc1z, hc12, hnear, hc1, hc2, hstrictPair,
      hc1P, hc2P⟩ :=
    exists_strictHeightCarrierPair_with_property_of_canonicalSuffixFrom S adm
      hdensity.execution.canonicalSuffixFrom hrec
      (z - a) a z (Nat.le_refl _) (w4pcs_nat_q0_le_carrier hstart haLo)
      hafterA ha haP hz haz haStrict hzgapHor
  have hc1Bound : c1 ≤ start + 4 * rawLag + 3 * gap + 4 :=
    w4pcs_nat_c1_bound_of_window haHi hzHi hc1z
  have hc2Bound : c2 ≤ start + 4 * rawLag + 3 * gap + 4 :=
    w4pcs_nat_c2_bound_of_window haHi hzHi hc1z hnear
  have hc1Above : start + 2 * rawLag < c1 :=
    w4pcs_nat_c1_above_of_window haLo hac1
  have hc2Above : start + 2 * rawLag < c2 :=
    w4pcs_nat_lt_trans_round hc1Above hc12
  have hsource1 : honestHMaxAt S rho (S.a start) <
      carrierOpeningHeight S rho c1 :=
    carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor S adm
      hdensity.frontierFloor hprogress hrawPos hstart hc1Above hc1
      (hstepHorSucc c1 hc1Bound)
  have hsource2 : honestHMaxAt S rho (S.a start) <
      carrierOpeningHeight S rho c2 :=
    carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor S adm
      hdensity.frontierFloor hprogress hrawPos hstart hc2Above hc2
      (hstepHorSucc c2 hc2Bound)
  refine ⟨c1, c2, hc1Above, hc12, hnear, hc2Bound, hc1, hc2, hsource1,
    hsource2, ?_, hc1P, hc2P⟩
  exact justifiableOpening_of_strict_carrierPair_of_carrierBand S
    hdensity.carrierBand
    (w4pcs_nat_q0_succ_lt_carrier hstart hrawPos hc1Above) hc12 hnear hgap
    hc1 hc2 (hstepHorSucc c1 hc1Bound) (hstepHorSucc c2 hc2Bound)
    (w4pcs_nat_le_of_le_of_lt
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
        (Assembly.a_mono S hstart)) hsource1)
    hstrictPair

#print axioms exists_justifiableCarrierPair_afterTwoProgress_with_property_prepared

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
