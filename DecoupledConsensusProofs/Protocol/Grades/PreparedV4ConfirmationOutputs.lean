module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4LiveSelection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedV4ConfirmationWalk

@[expose] public section

/-! # Prepared V4 confirmation outputs -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A named prepared confirmation walk gives the actual genuine write. -/
theorem SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_confirmationWalk : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v : V}, v ∈ rho.honest → ∀ {B : Block V},
        (∀ x ∈ rho.honest, Block.Preceq B (voterHeadAt S rho x s)) →
        Block.Preceq B
            (namedConfirmationWalk S
              (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) ∧
          confirmationEligible S.E
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
            (namedConfirmationWalk S
              (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) = true)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationAt S rho v s := by
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho v s
  let contract := NamedProfile.gradeContract read.cache
  have hwalk := _of_confirmationWalk hs hhor hv
    (B := Block.genesis)
    (fun x _ => Protocol.preceq_genesis (voterHeadAt S rho x s))
  unfold GenuineConfirmationAt
  change (rho.storeAt S v
      (Protocol.confirmation_time S.E s)).live_confirmed =
        namedConfirmationWalk S read s ∧
      confirmationEligible S.E read.st.core s
        (namedConfirmationWalk S read s) = true
  constructor
  · rw [live_confirmed_eq_update
      S adm.toNamedScheduleWellFormed hv s hhor]
    change (Protocol.update_confirmation_with contract S.E S.hc
      read.st.core s).live_confirmed = namedConfirmationWalk S read s
    rw [update_confirmation_with_live_confirmed, if_pos (by
      simpa only [read] using hwalk.2)]
    rfl
  · simpa only [read] using hwalk.2

#print axioms SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_pins

/-- Genuine confirmation prebuilt over only the two named read-fact pins. -/
theorem SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_anchor_band_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_anchor : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {w x : V}, w ∈ rho.honest → x ∈ rho.honest →
        Block.Preceq
          (namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
          (voterHeadAt S rho x s))
    (_of_band : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v x : V}, x ∈ rho.honest →
      ∀ {X : NamedBlock V}, X.erase = voterHeadAt S rho x s →
        NamedRun.blockInRun S rho X →
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg X).h)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationAt S rho v s := by
  exact SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun {s} hs' hhor' {v} hv' {B} hheads =>
        SettledBootstrapPreparedV4.confirmationWalk_core_of_pins
          S adm hcom hboot hawake hfinality _of_anchor _of_band
            hs' hhor' hv' hheads)
      hs hhor hv

#print axioms SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_anchor_band_pins

/-- A later named prepared confirmation extends each covered earlier live value. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_confirmationWalk : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v : V}, v ∈ rho.honest → ∀ {B : Block V},
        (∀ x ∈ rho.honest, Block.Preceq B (voterHeadAt S rho x s)) →
        Block.Preceq B
            (namedConfirmationWalk S
              (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) ∧
          confirmationEligible S.E
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
            (namedConfirmationWalk S
              (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) = true)
    (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {t : Time}
    (htlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t)
    (hthi : t < Protocol.confirmation_time S.E s) :
    Block.Preceq (rho.storeAt S w t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed := by
  have hwalk := _of_confirmationWalk hs hhor hv
    (B := (rho.storeAt S w t).live_confirmed)
    (fun x hx =>
      SettledBootstrapPreparedV4.liveConfirmed_at_read_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hs (Nat.le_succ s)
          htlo hthi hw hx)
  rw [live_confirmed_eq_update
    S adm.toNamedScheduleWellFormed hv s hhor]
  change Block.Preceq (rho.storeAt S w t).live_confirmed
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s).live_confirmed
  have helig := hwalk.2
  change confEligible S.E
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
      (confWalkWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
        S.E S.hc
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s) = true
    at helig
  rw [update_confirmation_with_live_confirmed, if_pos helig]
  simpa only [namedConfirmationWalk] using hwalk.1

#print axioms SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_pins

/-- Live-at-confirmation growth prebuilt over only the named anchor and band pins. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_anchor_band_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_anchor : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {w x : V}, w ∈ rho.honest → x ∈ rho.honest →
        Block.Preceq
          (namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
          (voterHeadAt S rho x s))
    (_of_band : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v x : V}, x ∈ rho.honest →
      ∀ {X : NamedBlock V}, X.erase = voterHeadAt S rho x s →
        NamedRun.blockInRun S rho X →
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg X).h)
    (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {t : Time}
    (htlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t)
    (hthi : t < Protocol.confirmation_time S.E s) :
    Block.Preceq (rho.storeAt S w t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed := by
  exact SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun {s} hs' hhor' {v} hv' {B} hheads =>
        SettledBootstrapPreparedV4.confirmationWalk_core_of_pins
          S adm hcom hboot hawake hfinality _of_anchor _of_band
            hs' hhor' hv' hheads)
      hs hhor hv hw htlo hthi

#print axioms SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_anchor_band_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
