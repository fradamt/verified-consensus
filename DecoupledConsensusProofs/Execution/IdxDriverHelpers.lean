module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverHelpers
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Named ancestry is transitive (public copy) -/

omit [Fintype V] in
theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    have hB : B = .genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hBC
    exact hB ▸ hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hBC
    rcases hBC with rfl | hBp
    · exact hAB
    · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (ih hBp)

/-! ## 2. Witness monotonicity -/



/-! ## 3. Base case: the empty prefix, witness `.genesis` -/

theorem jointHistoryIdx_zero (S : Setup V) (rho : NamedRun V)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    LayerAJointHistoryIdx S rho 0 (.genesis : NamedBlock V) := by
  have hgen := JointHistoryProducersTime.genesis_in_run S rho hbad
  refine ⟨⟨hgen, ?_, ?_, ?_⟩, ?_, ?_, Or.inl rfl⟩
  · intro i v ta a hv he hmem hlt
    exact absurd hlt (Nat.not_lt_zero i)
  · intro i v ta a hv he hmem hlt
    exact absurd hlt (Nat.not_lt_zero i)
  · intro i v hv hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    have hv0 : (NamedRun.stateBefore S rho 0 v).st.bodies = {(.genesis : NamedBlock V)} := by
      show (NamedNode.initial : NamedNodeState V).st.bodies = {(.genesis : NamedBlock V)}
      simp [NamedNode.initial, Protocol.NamedStore.initial]
    have hF0 : (NamedRun.stateBefore S rho 0 v).st.core.F = Block.genesis := by
      show (NamedNode.initial : NamedNodeState V).st.core.F = Block.genesis
      simp only [NamedNode.initial, Protocol.NamedStore.initial]
      rfl
    refine ⟨.genesis, hgen, ?_, hF0, JointHistoryProducersTime.named_preceq_self _⟩
    rw [hv0]; exact Finset.mem_singleton_self _
  · intro i v ta a hv he hmem hlt
    exact absurd hlt (Nat.not_lt_zero i)
  · intro i v r hv he hlt
    exact absurd hlt (Nat.not_lt_zero i)

theorem witnessProvenanceIdx_mono (S : Setup V) (rho : NamedRun V)
    {n m : Nat} {C : NamedBlock V} (h : WitnessProvenanceIdx S rho n C)
    (hle : n ≤ m) : WitnessProvenanceIdx S rho m C := by
  rcases h with rfl | ⟨i, v, r, hin, hv, he, hbody, hroot⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, v, r, hin.trans hle, hv, he, hbody, hroot⟩

/-! ## 4. `stateBefore` is stable across an event-free index -/

theorem stateBefore_stable (S : Setup V) (rho : NamedRun V) (v : V) {n : Nat}
    (hn : rho.events.length ≤ n) :
    NamedRun.stateBefore S rho (n + 1) v = NamedRun.stateBefore S rho n v := by
  have hnone : rho.events[n]? = none := List.getElem?_eq_none hn
  rw [Proofs.NamedRuntime.stateBefore_succ, hnone]
  simp

/-! ## 5. The joint history package is stable across an event-free index -/

theorem jointHistoryIdx_succ_no_event (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) (hn : rho.events.length ≤ n)
    (h : LayerAJointHistoryIdx S rho n C) : LayerAJointHistoryIdx S rho (n + 1) C := by
  obtain ⟨⟨hblock, h1, h2, h3⟩, hSG, hConf, hprov⟩ := h
  refine ⟨⟨hblock, ?_, ?_, ?_⟩, ?_, ?_,
    witnessProvenanceIdx_mono S rho hprov (Nat.le_succ _ )⟩
  · intro i v ta a hv he hmem hlt fp hfp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h1 i v ta a hv he hmem hlt' fp hfp
    · exfalso; have hlen := (List.getElem?_eq_some_iff.mp he).1; omega
  · intro i v ta a hv he hmem hlt hh T timeout hp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h2 i v ta a hv he hmem hlt' hh T timeout hp
    · exfalso; have hlen := (List.getElem?_eq_some_iff.mp he).1; omega
  · intro i v hv hile
    rcases (by omega : i ≤ n ∨ i = n + 1) with hile' | rfl
    · exact h3 i v hv hile'
    · have heq := stateBefore_stable S rho v hn
      obtain ⟨F, hFrun, hFbod, hFerase, hFpre⟩ := h3 n v hv le_rfl
      refine ⟨F, hFrun, ?_, ?_, hFpre⟩
      · rw [heq]; exact hFbod
      · rw [heq]; exact hFerase
  · intro i v ta a hv he hmem hlt key hkey
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact hSG i v ta a hv he hmem hlt' key hkey
    · exfalso; have hlen := (List.getElem?_eq_some_iff.mp he).1; omega
  · intro i v r hv he hlt
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact hConf i v r hv he hlt'
    · exfalso; have hlen := (List.getElem?_eq_some_iff.mp he).1; omega

/-! ## 6-9. Boundary-index facts -/

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- Converse direction of `tick_index_lt_boundaryIdx`: every
event below the `≤ cap` boundary has time at most `cap`. -/
theorem time_le_of_lt_boundaryIdx (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {e : NamedEvent V} {t : Time} (he : rho.events[i]? = some e)
    (hi : i < boundaryIdx rho t) : e.time ≤ t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
  have hdropNil : (rho.events.drop i).filter (fun x => decide (x.time ≤ t)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [decide_eq_true_eq, not_le]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hkRun : rho.events[i + k]? = some x := by rwa [List.getElem?_drop] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Nat.add_zero] at hkRun
      have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      rwa [hxe]
    · have hilt : i < i + k := by omega
      obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp sorted) i (i + k) hiLen hkLen hilt
      rw [hiGet, hkGet] at hkey
      exact hcon.trans_le (time_le_of_key_le hkey)
  have hsplit : rho.events.filter (fun x => decide (x.time ≤ t)) =
      (rho.events.take i).filter (fun x => decide (x.time ≤ t)) ++
      (rho.events.drop i).filter (fun x => decide (x.time ≤ t)) := by
    conv_lhs => rw [← List.take_append_drop i rho.events]
    rw [List.filter_append]
  have hbound : boundaryIdx rho t ≤ i := by
    unfold boundaryIdx
    rw [hsplit, hdropNil, List.append_nil]
    calc ((rho.events.take i).filter (fun x => decide (x.time ≤ t))).length
        ≤ (rho.events.take i).length := List.length_filter_le _ _
      _ ≤ i := by rw [List.length_take]; exact Nat.min_le_left _ _
  omega



omit [DecidableEq V] [Fintype V] in
theorem hcapn_of_le_boundaryIdx (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {n : Nat} {cap : Time} (hn : n ≤ boundaryIdx rho cap) :
    ∀ i, i < n → ∀ e : NamedEvent V, rho.events[i]? = some e → e.time ≤ cap := by
  intro i hi e he
  exact time_le_of_lt_boundaryIdx rho sorted he (lt_of_lt_of_le hi hn)

#print axioms jointHistoryIdx_zero
#print axioms stateBefore_stable
#print axioms jointHistoryIdx_succ_no_event
#print axioms time_le_of_lt_boundaryIdx
#print axioms hcapn_of_le_boundaryIdx

end DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverHelpers

end
