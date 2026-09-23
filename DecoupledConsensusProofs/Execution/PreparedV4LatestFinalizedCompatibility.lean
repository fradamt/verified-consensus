module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4FinalizedHeadCore

@[expose] public section

/-! # Latest/finalized compatibility after the prepared V4 handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_confirmationHorizon_max_compat
    (S : Setup V) {rho : Run V} {s t : Slot}
    (hs : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (ht : Protocol.confirmation_time S.E t ≤ rho.horizon) :
    Protocol.confirmation_time S.E (max s t) ≤ rho.horizon := by
  rcases le_total s t with h | h
  · simpa only [max_eq_right h] using ht
  · simpa only [max_eq_left h] using hs

/-- The actual latest and finalized source slots have a common later honest
vote head. -/
theorem SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (latest_has_voteHead_bound_core_of_pins :
      ∀ {v : V}, v ∈ rho.honest → ∀ {t : Time},
      Protocol.confirmation_time S.E start ≤ t →
      ∃ first : Slot, start ≤ first ∧
        Protocol.confirmation_time S.E first ≤ rho.horizon ∧
        ∀ last, first ≤ last →
          Protocol.confirmation_time S.E last ≤ rho.horizon →
          ∀ x ∈ rho.honest,
            Block.Preceq (rho.storeAt S v t).core.latest_confirmed
              (voterHeadAt S rho x (last + 1)))
    (finalized_has_voteHead_bound_core_of_pins :
      ∀ {w : V}, w ∈ rho.honest → ∀ {u : Time},
      Protocol.confirmation_time S.E start ≤ u →
      ∃ first : Slot, start ≤ first ∧
        Protocol.confirmation_time S.E first ≤ rho.horizon ∧
        ∀ last, first ≤ last →
          Protocol.confirmation_time S.E last ≤ rho.horizon →
          ∀ x ∈ rho.honest,
            Block.Preceq (rho.storeAt S w u).core.F
              (voterHeadAt S rho x (last + 1)))
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t)
    (hu : Protocol.confirmation_time S.E start ≤ u)
    (htHor : t ≤ rho.horizon) (huHor : u ≤ rho.horizon) :
    Block.compatible (rho.storeAt S v t).core.latest_confirmed
      (rho.storeAt S w u).core.F = true := by
  obtain ⟨q, _, hqHor, hlatest⟩ :=
    latest_has_voteHead_bound_core_of_pins hv ht
  obtain ⟨r, _, hrHor, hfinalized⟩ :=
    finalized_has_voteHead_bound_core_of_pins hw hu
  have hnonempty : 0 < ((S.E.committee start) ∩ rho.honest).card := by
    have hm := hcom start
    rcases Nat.eq_zero_or_pos ((S.E.committee start) ∩ rho.honest).card with
      hz | hp
    · rw [hz, Nat.mul_zero] at hm
      exact absurd hm (Nat.not_lt_zero _)
    · exact hp
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hnonempty
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
  let last := max q r
  have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon :=
    preparedV4_confirmationHorizon_max_compat S hqHor hrHor
  exact Block.compatible_of_preceq_common
    (hlatest last (Nat.le_max_left _ _) hlastHor x hx)
    (hfinalized last (Nat.le_max_right _ _) hlastHor x hx)

#print axioms SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_pins


/-- Item 16 is closed; only the item-14 latest-record bound remains pinned. -/
theorem SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_latest_pin
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    (latest_has_voteHead_bound_core_of_pins :
      ∀ {v : V}, v ∈ rho.honest → ∀ {t : Time},
      Protocol.confirmation_time S.E start ≤ t →
      ∃ first : Slot, start ≤ first ∧
        Protocol.confirmation_time S.E first ≤ rho.horizon ∧
        ∀ last, first ≤ last →
          Protocol.confirmation_time S.E last ≤ rho.horizon →
          ∀ x ∈ rho.honest,
            Block.Preceq (rho.storeAt S v t).core.latest_confirmed
              (voterHeadAt S rho x (last + 1)))
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t)
    (hu : Protocol.confirmation_time S.E start ≤ u)
    (htHor : t ≤ rho.horizon) (huHor : u ≤ rho.horizon) :
    Block.compatible (rho.storeAt S v t).core.latest_confirmed
      (rho.storeAt S w u).core.F = true := by
  exact SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_pins
    S adm hcom hboot hlatest hawake hfinality hstartHor
      latest_has_voteHead_bound_core_of_pins
      (fun {w} hw {u} hu =>
        SettledBootstrapPreparedV4.finalized_has_voteHead_bound_core
          S adm hcom hboot hawake hfinality hstartHor
            (w := w) hw (u := u) hu)
      hv hw ht hu htHor huHor

#print axioms SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_latest_pin

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
