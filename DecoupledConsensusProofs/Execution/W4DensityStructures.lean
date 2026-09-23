module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.CanonicalDensityDischarge
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # The prepared density record, placed below the assembly

`CanonicalCarrierDensityFromPrepared` is the corresponding branch's additive twin of
`CanonicalCarrierDensityFrom` (`CanonicalDensityDischargeRun.lean:524`), with
the execution field at the prepared contract and the two counting fields
verbatim.

It is declared here rather than in `W4FKRegimeRun` for a layering reason. That
module imports `W4D3FinalitySpineComposeRun`, which is where the corresponding branch's
density pin lives, so a record declared there sits ABOVE the assembly and the
assembly cannot state a pin whose conclusion is that record without a cycle.
This leaf imports only the module that declares the plain record and the module
that declares the prepared execution record, so everything that needs the
prepared density record can reach it.

Nothing else belongs here: it is a placement leaf, not a proof leaf. The
producers stay with the corresponding branch. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The density interface over the prepared execution record. The two counting
fields are those of `CanonicalCarrierDensityFrom`, unchanged. -/
structure CanonicalCarrierDensityFromPrepared
    (S : Setup V) (rho : Run V) (q0 : Round) : Prop where
  execution : CanonicalSuffixExecutionPrepared S rho q0
  carrierBand : ∀ c1 c2 : Round, q0 + 1 < c1 → c1 < c2 →
    ProposerCarrierAt S rho c1 → ProposerCarrierAt S rho c2 →
    S.a (c1 + 1) ≤ rho.horizon → S.a (c2 + 1) ≤ rho.horizon →
    honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c1 →
      carrierOpeningHeight S rho c2 ≤
        carrierOpeningHeight S rho c1 + (c2 - c1)
  frontierFloor : ∀ r c : Round, q0 < r → r < c →
    ProposerCarrierAt S rho c → S.a (c + 1) ≤ rho.horizon →
    honestHMaxAt S rho (S.a q0) + 2 ≤ honestHMaxAt S rho (S.a r) →
      honestHMaxAt S rho (S.a r) - 1 ≤ carrierOpeningHeight S rho c

/-! ## Field-level consumers of the prepared density record

The three consumers below read only `frontierFloor` or `carrierBand`. They are
therefore restated over those fields, rather than over the prepared record's
contract-bearing `execution` field. The arithmetic helpers are copied from
`CanonicalDensityDischargeRun.lean:700-730,954-963,978-998`; they are private
there and are prefixed here for this clean leaf.
-/

private theorem w4ds_nat_gain_trans {A B C : Nat}
    (h1 : A ≤ B) (h2 : B + 2 ≤ C) : A + 2 ≤ C := by omega

private theorem w4ds_nat_lt_of_gain_and_floor {a b c : Nat}
    (hgain : a + 2 ≤ b) (hfloor : b - 1 ≤ c) : a < c := by omega

private theorem w4ds_nat_q0_lt_progressWindow {q0 start rawLag : Nat}
    (hstart : q0 ≤ start) (hraw : 0 < rawLag) :
    q0 < start + 2 * rawLag := by omega

private theorem w4ds_nat_recurrence_window
    {start rawLag gap first : Nat}
    (h : first ≤ start + 2 * rawLag + 1 + gap) :
    first + 1 ≤ start + 2 * rawLag + 1 + gap + 1 := by omega

private theorem w4ds_nat_above_of_window
    {start rawLag first : Nat}
    (h : start + 2 * rawLag + 1 ≤ first) :
    start + 2 * rawLag < first := by omega

private theorem w4ds_nat_band_of_carrierBand
    {H1 H2 c1 c2 gap K : Nat}
    (hupper : H2 ≤ H1 + (c2 - c1))
    (hnear : c2 ≤ c1 + gap + 1)
    (hgap : gap + 2 ≤ K) : H2 < H1 + K := by omega

/-- The frontier-floor consumer over the prepared record's verbatim field. -/
theorem carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 rawLag start first : Round}
    (hfrontierFloor : ∀ r c : Round, q0 < r → r < c →
      ProposerCarrierAt S rho c → S.a (c + 1) ≤ rho.horizon →
      honestHMaxAt S rho (S.a q0) + 2 ≤ honestHMaxAt S rho (S.a r) →
        honestHMaxAt S rho (S.a r) - 1 ≤ carrierOpeningHeight S rho c)
    (hprogress : EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos : 0 < rawLag)
    (hstart : q0 ≤ start)
    (hfirst : start + 2 * rawLag < first)
    (hcarrier : ProposerCarrierAt S rho first)
    (hfirstHor : S.a (first + 1) ≤ rho.horizon) :
    honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho first := by
  have hendHor : S.a (start + 2 * rawLag) ≤ rho.horizon :=
    (Assembly.a_mono S ((Nat.le_of_lt hfirst).trans (Nat.le_succ first))).trans
      hfirstHor
  have hgain := eventualHeightProgress_iterate S hprogress hstart 2 hendHor
  have hq0gain : honestHMaxAt S rho (S.a q0) + 2 ≤
      honestHMaxAt S rho (S.a (start + 2 * rawLag)) :=
    w4ds_nat_gain_trans
      (honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Assembly.a_mono S hstart)) hgain
  have hfloor := hfrontierFloor (start + 2 * rawLag) first
    (w4ds_nat_q0_lt_progressWindow hstart hrawPos) hfirst hcarrier
      hfirstHor hq0gain
  exact w4ds_nat_lt_of_gain_and_floor hgain hfloor

#print axioms carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor

/-- The recurrence consumer over the prepared record's verbatim field. -/
private theorem w4ds_select_bounds_nat {q0 start rawLag gap : Nat}
    (hstart : q0 ≤ start) :
    q0 < start + 2 * rawLag + 1 ∧
      start + 2 * rawLag + 1 + gap ≤
        start + 2 * rawLag + 1 + gap + 1 := by
  omega

theorem carrierOpening_height_gt_of_twoProgress_carrier_of_frontierFloor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 rawLag gap start : Round}
    (hfrontierFloor : ∀ r c : Round, q0 < r → r < c →
      ProposerCarrierAt S rho c → S.a (c + 1) ≤ rho.horizon →
      honestHMaxAt S rho (S.a q0) + 2 ≤ honestHMaxAt S rho (S.a r) →
        honestHMaxAt S rho (S.a r) - 1 ≤ carrierOpeningHeight S rho c)
    (hprogress : EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos : 0 < rawLag)
    (hrec : MultiProposerRecurrence S rho gap)
    (hpost : S.E.t_GST ≤ S.a q0)
    (hstart : q0 ≤ start)
    (hhor : S.a (start + 2 * rawLag + 1 + gap + 1) ≤ rho.horizon) :
    ∃ first : Round,
      start + 2 * rawLag < first ∧
        first ≤ start + 2 * rawLag + 1 + gap ∧
        ProposerCarrierAt S rho first ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho first := by
  obtain ⟨hfirstGST, hfirstEnd⟩ :=
    w4ds_select_bounds_nat (rawLag := rawLag) (gap := gap) hstart
  obtain ⟨first, hfirstLo, hfirstHi, hcarrier⟩ :=
    hrec (start + 2 * rawLag + 1)
      (hpost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (action_add_delta_le_openingProposal_of_round_lt S hfirstGST)))
      ((openingProposal_window_le_action S (start + 2 * rawLag + 1) gap).trans
        ((Assembly.a_mono S hfirstEnd).trans hhor))
  have hfirst : start + 2 * rawLag < first :=
    w4ds_nat_above_of_window hfirstLo
  have hfirstHor : S.a (first + 1) ≤ rho.horizon :=
    (Assembly.a_mono S (w4ds_nat_recurrence_window hfirstHi)).trans hhor
  exact ⟨first, hfirst, hfirstHi, hcarrier,
    carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor
      S adm hfrontierFloor hprogress hrawPos hstart hfirst hcarrier hfirstHor⟩

#print axioms carrierOpening_height_gt_of_twoProgress_carrier_of_frontierFloor

/-- The justifiability consumer over the prepared record's verbatim field. -/
theorem justifiableOpening_of_strict_carrierPair_of_carrierBand
    (S : Setup V) {rho : Run V}
    {q0 gap c1 c2 : Round}
    (hcarrierBand : ∀ c1 c2 : Round, q0 + 1 < c1 → c1 < c2 →
      ProposerCarrierAt S rho c1 → ProposerCarrierAt S rho c2 →
      S.a (c1 + 1) ≤ rho.horizon → S.a (c2 + 1) ≤ rho.horizon →
      honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c1 →
        carrierOpeningHeight S rho c2 ≤
          carrierOpeningHeight S rho c1 + (c2 - c1))
    (hq0 : q0 + 1 < c1) (hc12 : c1 < c2)
    (hnear : c2 ≤ c1 + gap + 1)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hc1 : ProposerCarrierAt S rho c1) (hc2 : ProposerCarrierAt S rho c2)
    (hhor1 : S.a (c1 + 1) ≤ rho.horizon)
    (hhor2 : S.a (c2 + 1) ≤ rho.horizon)
    (hold : honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c1)
    (hstrict : carrierOpeningHeight S rho c1 <
      carrierOpeningHeight S rho c2) :
    ∃ P1 P2 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot c1) = some P1 ∧
      proposedBlockAt S rho (S.hc.opening_slot c2) = some P2 ∧
      ((Protocol.derive_named S.E S.cfg P1).nj = false ∨
        (Protocol.derive_named S.E S.cfg P2).nj = false) := by
  have hupper := hcarrierBand c1 c2 hq0 hc12 hc1 hc2 hhor1 hhor2 hold
  refine ⟨canonicalProposal S rho (S.hc.opening_slot c1),
    canonicalProposal S rho (S.hc.opening_slot c2),
    canonicalProposal_spec S rho (S.hc.opening_slot c1),
    canonicalProposal_spec S rho (S.hc.opening_slot c2), ?_⟩
  exact named_derive_nj_eq_false_left_or_right_of_strict_band S.E S.cfg
    (by simpa only [carrierOpeningHeight] using hstrict)
    (by
      simpa only [carrierOpeningHeight] using
        (w4ds_nat_band_of_carrierBand hupper hnear hgap))

#print axioms justifiableOpening_of_strict_carrierPair_of_carrierBand

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
