module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4LiveSelection
public import DecoupledConsensusProofs.Execution.PreparedV4ActionSourcesCore

@[expose] public section

/-! # Prepared V4 live selection at the actual vote horizon -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem protectedVoteSlot_of_coreHeads_v4
    (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x d)) :
    ProtectedVoteSlot S rho d B := by
  refine ⟨hheads, ?_⟩
  intro x hx hxc
  obtain ⟨X, hX, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits S adm hx hd hxc hhor
  exact ⟨X, by simpa only [hX] using hheads x hx, hXrun, hXemit⟩

private theorem protectedVoteSlot_succ_of_heads_at_vote_v4
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ s) (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V}
    (hheads : ∀ x ∈ rho.honest, Block.Preceq B (voterHeadAt S rho x s)) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hcutpos : 0 < base + S.hc.η_SG :=
    (Nat.zero_lt_of_lt S.hc.η_SG_ge_one).trans_le (Nat.le_add_left _ _)
  have hs : 0 < s :=
    (Nat.mul_pos hcutpos
      (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)).trans_le
        (hboot.settled.trans hd)
  have hshor := (vote_time_mono_slots S.E (Nat.le_succ s)).trans hhor
  have hseed := SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core
    S adm hcom hboot hawake hfinality hd hshor
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have h := hcom s
    omega
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hpositive
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
  have hcomp := Block.compatible_of_preceq_common
    (hseed.heads x hx) (hheads x hx)
  simp only [Block.compatible, Bool.or_eq_true] at hcomp
  rcases hcomp with hPB | hBP
  · exact SettledBootstrapPreparedV4.protectedVoteSlot_succ_at_vote_core
      S adm hcom hboot hawake hfinality hd hhor hPB
        (protectedVoteSlot_of_coreHeads_v4 S adm hs hshor hheads)
  · exact (SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core
      S adm hcom hboot hawake hfinality (hd.trans (Nat.le_succ s)) hhor).of_ancestor hBP


/-- A prepared confirmation selection before a strict later destination is
protected at that destination's actual vote horizon. -/
theorem SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_after_start_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start q d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start < d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hq : S.hc.opening_slot (base + S.hc.η_SG) ≤ q)
    (hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon) (hqd : q < d)
    {w : V} (hw : w ∈ rho.honest) :
    ProtectedVoteSlot S rho d
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q).live_confirmed := by
  cases d with
  | zero => exact False.elim ((Nat.not_lt_zero start) hd)
  | succ s =>
      have hds : start ≤ s := Nat.le_of_lt_succ hd
      have hcutpos : 0 < base + S.hc.η_SG :=
        (Nat.zero_lt_of_lt S.hc.η_SG_ge_one).trans_le (Nat.le_add_left _ _)
      have hs : 0 < s :=
        (Nat.mul_pos hcutpos
          (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)).trans_le
            (hboot.settled.trans hds)
      by_cases hqs : q = s
      · subst q
        exact protectedVoteSlot_of_coreHeads_v4 S adm (Nat.zero_lt_succ s) hhor
          (fun x hx =>
            SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core
              S adm hcom hboot hawake hfinality
                (last := s) (d := s + 1) (q := s)
                hqhor hd.le (le_refl _) hq hqd hw hx)
      · have hqslt : q < s :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hqd) hqs
        have hprevHor : Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon := by
          rw [Protocol.confirmation_time_eq_support_cutoff_succ,
            Nat.sub_add_cancel hs]
          exact (support_cutoff_le_vote_time_succ S.E s).trans hhor
        exact protectedVoteSlot_succ_of_heads_at_vote_v4
          S adm hcom hboot hawake hfinality hds hhor
            (fun x hx =>
              SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core
                S adm hcom hboot hawake hfinality
                  (last := s - 1) (d := s) (q := q) hprevHor hds
                  (Nat.sub_add_cancel hs).symm.le hq hqslt hw hx)

#print axioms SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_after_start_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
