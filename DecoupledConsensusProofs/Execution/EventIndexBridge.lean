module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices

@[expose] public section

/-!
# Index/time bridge facts (tasks 1-2)

`emission_index_lt_acceptance` proves `EmissionIndexQuery`: an honest
object processed (delivered or self-processed) at event index `j` was
emitted by its honest author at a tick of index `< j`. The carried-row
variants give the same bound for a row/GF vote carried by a delivered
block. `jointHistoryOn_of_idx` proves `JointHistoryOnOfIdxQuery`: the
time-based joint history at `t` follows from the index-bounded joint
history at `boundaryIdx rho t`.
-/


namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le


/-- A tick of index `k` cannot be at or after a delivery of index `j` when
the tick's time is `≤` the delivery's time: the sorted event key orders
ticks strictly before deliveries at the same instant. Public: reused by the
viability-history index migration (task 3) against a specific known tick,
not only through the packaged existentials above. -/
theorem tick_lt_of_deliver_index (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {j k : Nat} {v : V} {o : NamedObject V} {t : Time} {u : V} {t' : Time}
    (hj : rho.events[j]? = some (.deliver v o t))
    (hk : rho.events[k]? = some (.tick u t'))
    (ht' : t' ≤ t) : k < j := by
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp sorted) j k hjLen hkLen hlt
    rw [hjGet, hkGet] at hkey
    simp only [NamedEvent.key, NamedEvent.time, NamedEvent.phase] at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt2 | ⟨heq2, hphase⟩
    · exact absurd ht' (not_le.mpr hlt2)
    · dsimp only at hphase
      omega
  · rw [← heq] at hk
    rw [hj] at hk
    injection hk with hk'
    injection hk'


/-- Carried-row variant: an honest attestation carried by a block delivered
at index `j` was emitted by its honest author at a tick of index `< j`. -/
theorem emission_index_lt_acceptance_carried_attest
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (j : Nat) (v : V) (B : NamedBlock V) (t : Time)
    (hj : rho.events[j]? = some (.deliver v (.block B) t))
    (a : NamedAttestation V) (ha : a ∈ B.attestations) (hu : a.val_index ∈ rho.honest) :
    ∃ (k : Nat) (t' : Time), k < j ∧ rho.events[k]? = some (.tick a.val_index t') ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index t' := by
  have hprocesses : NamedRun.processes S rho v (.block B) t := Or.inr ⟨j, hj⟩
  obtain ⟨t', ht', hemits⟩ := core.carried_attest v B t hprocesses a ha hu
  obtain ⟨k, hk, hemit⟩ := hemits
  exact ⟨k, t', tick_lt_of_deliver_index rho core.sorted hj hk ht', hk, hemit⟩



/-- Every tick with time `< t` sits below the `≤ t` boundary. Public: reused by
the ready-head-kernel index migration (idx batch 2a task 3), which needs the
`boundaryIdx` bound on an arbitrary strict-read prefix. -/
theorem tick_index_lt_boundaryIdx (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {e : NamedEvent V} {t : Time} (he : rho.events[i]? = some e)
    (ht : e.time < t) : i < boundaryIdx rho t := by
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (i + 1)).filter (fun x => decide (x.time ≤ t)) =
      rho.events.take (i + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < i + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hki | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp sorted) k i hkLen hiLen hki
      rw [hkGet, hiGet] at hkey
      exact ((time_le_of_key_le hkey).trans_lt ht).le
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht.le
  have hsplit : rho.events.filter (fun x => decide (x.time ≤ t)) =
      (rho.events.take (i + 1)).filter (fun x => decide (x.time ≤ t)) ++
      (rho.events.drop (i + 1)).filter (fun x => decide (x.time ≤ t)) := by
    conv_lhs => rw [← List.take_append_drop (i + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hiLen)] at hlength
  unfold boundaryIdx
  omega


/-- Every `PrefixThrough rho i t` index sits at or below the `≤ t` boundary.
Public: reused by the ready-head-kernel index migration (idx batch 2a task 3). -/
theorem prefixThrough_le_boundaryIdx (rho : NamedRun V) {i : Nat} {t : Time}
    (hprefix : PrefixThrough rho i t) : i ≤ boundaryIdx rho t := by
  obtain ⟨hiLen, hbound⟩ := hprefix
  have htake : (rho.events.take i).filter (fun x => decide (x.time ≤ t)) =
      rho.events.take i := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < i := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    exact hbound k hklt x hkRun
  have hsplit : rho.events.filter (fun x => decide (x.time ≤ t)) =
      (rho.events.take i).filter (fun x => decide (x.time ≤ t)) ++
      (rho.events.drop i).filter (fun x => decide (x.time ≤ t)) := by
    conv_lhs => rw [← List.take_append_drop i rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take, Nat.min_eq_left hiLen] at hlength
  unfold boundaryIdx
  omega


#print axioms emission_index_lt_acceptance_carried_attest

end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
