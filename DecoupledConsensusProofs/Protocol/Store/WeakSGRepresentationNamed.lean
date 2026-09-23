module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Schedule.Action

@[expose] public section

/-!
# SG representation under core admissibility

This is the named-runtime producer for the weak SG window. An awake honest
action emits its named attestation at `S.a r`; named synchrony places an actual
handler call at the reader before the deadline, and named admission places the
attestation's SG projection in the reader's SG vote set.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (Proofs.Bridges.time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
private theorem post_index_le_strict_filter_length (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) :
    j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (Proofs.Bridges.time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

/-! The public theorem keeps the earlier hypotheses and conclusion, with the
named attestation erased only at the SG projection boundary. -/
theorem awake_sgVote_mem_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {t : Time} (hA : (S.node v).awake r = true)
    (hpost : S.E.t_GST ≤ S.a r) (hread : S.a r + S.E.Δ ≤ t)
    (hhor : t ≤ rho.horizon) :
    Protocol.sgVote (actionAttestationAt S rho v r).erase ∈
      (rho.stateBeforeTime S t w).st.toHealing.sg_votes r := by
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon := hread.trans hhor
  have haction : S.a r ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hdeadline
  have hem := honest_emits_exact_actionAttestationAt_of_awake S
    adm.toNamedScheduleWellFormed hv r hA haction
  have hmax : max (S.a r) S.E.t_GST = S.a r := max_eq_left hpost
  obtain ⟨td, hcausal, htd, j, hcall⟩ :=
    adm.toNamedSynchrony.broadcast v hv (.attest (actionAttestationAt S rho v r))
      (S.a r) hem w hw (by simpa only [hmax] using hdeadline) rfl
  have hhi : td < S.a r + S.E.Δ := by simpa only [hmax] using htd
  have hval : (actionAttestationAt S rho v r).val_index ∈ rho.honest := by
    rw [(actionAttestationAt_shape S rho v r).1]
    exact hv
  have hem' : NamedRun.emits S rho
      (actionAttestationAt S rho v r).val_index
      (.attest (actionAttestationAt S rho v r))
      (S.a (actionAttestationAt S rho v r).round) := by
    simpa only [(actionAttestationAt_shape S rho v r).1,
      (actionAttestationAt_shape S rho v r).2.1] using hem
  have hlo : S.a (actionAttestationAt S rho v r).round ≤ td := by
    simpa only [(actionAttestationAt_shape S rho v r).2.1] using hcausal
  have hhi' : td < S.a (actionAttestationAt S rho v r).round + S.E.Δ := by
    simpa only [(actionAttestationAt_shape S rho v r).2.1] using hhi
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    adm.toNamedScheduleWellFormed adm.toNamedUnforgeable hval hem' hcall hlo hhi'
  obtain ⟨e, he, _, het⟩ := hcall.2
  have hindex := post_index_le_strict_filter_length rho adm.toNamedScheduleWellFormed.sorted t he
    (by simpa only [het] using hhi.trans_le hread)
  obtain ⟨hrow', -⟩ := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w hindex hrow
  have hreadEq : NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun x => decide (x.time < t))).length := by
    exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
      (strict_filter_eq_take rho adm.toNamedScheduleWellFormed.sorted t)
  have hheld : actionAttestationAt S rho v r ∈
      (rho.stateBeforeTime S t w).st.sg_rows r := by
    simpa only [hreadEq, (actionAttestationAt_shape S rho v r).2.1] using hrow'
  have hheld' : actionAttestationAt S rho v r ∈
      (rho.stateBeforeTime S t w).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    simpa only [(actionAttestationAt_shape S rho v r).2.1] using hheld
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hpool := NamedAdmission.pool_view_mem
    (rho.stateBeforeTime S t w).st hcoh.2.2.2.1
    (actionAttestationAt S rho v r) hheld'
  simpa only [(actionAttestationAt_shape S rho v r).2.1] using
    (Finset.mem_image_of_mem Protocol.sgVote hpool)

end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
