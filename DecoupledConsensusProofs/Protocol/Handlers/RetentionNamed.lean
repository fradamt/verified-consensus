module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick
public import DecoupledConsensusProofs.Execution.Runtime

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named handler chain -/

theorem on_block_using_latest (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [Protocol.update_finality_latest,
          Protocol.foldl_on_goldfish_vote_checked_latest]

omit [DecidableEq V] [Fintype V] in
theorem on_block_checked_using_latest (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_confirmed = st.latest_confirmed) :
    (Protocol.on_block_checked_using handle hc st B).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

omit [Fintype V] in
private theorem commitBlock_latest (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).latest_confirmed = after.latest_confirmed := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_latest (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_latest]
       exact on_block_checked_using_latest _ hc st.core B.erase
         (on_block_using_latest E st.core B.erase _))

omit [Fintype V] in
theorem admit_row_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact Protocol.on_sg_vote_latest hc st.core row.erase

omit [Fintype V] in
private theorem foldl_admit_row_latest (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_latest]

omit [Fintype V] in
theorem admit_rows_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).latest_confirmed = st.latest_confirmed :=
  foldl_admit_row_latest hc rows st

omit [Fintype V] in
theorem admit_carried_latest (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).latest_confirmed =
      after.latest_confirmed := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_latest hc after B.attestations
      · rfl

theorem on_block_with_latest (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_latest]
  exact process_block_core_latest E hc cfg st B









/-- Object receipt leaves the user record unchanged. -/
theorem node_process_latest (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).st.core.latest_confirmed = n.st.core.latest_confirmed := by
  cases o with
  | block B => exact on_block_with_latest .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact Protocol.on_goldfish_vote_checked_latest S.E n.st.core u
  | attest a => exact admit_row_latest S.hc n.st a


/-! ## Along the run -/


/-! ### The strict time read

`stateBeforeTime` at `t` is the `stateBefore` prefix whose length is the number
of events strictly before `t`. Three helpers of `NamedRuntime` are private
there; they are restated here with their original proofs. -/

omit [DecidableEq V] [Fintype V] in
private theorem key_time_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

omit [DecidableEq V] [Fintype V] in
private theorem lt_downward (t : Time) :
    ∀ e f : NamedEvent V, e.key ≤ f.key → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (key_time_le hk) hf

omit [DecidableEq V] [Fintype V] in
private theorem filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : NamedEvent V → Bool)
    (hdown : ∀ e f : NamedEvent V, e.key ≤ f.key → p f = true → p e = true) :
    rho.events.filter p = rho.events.take (rho.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- An event whose time is strictly below `t` sits strictly inside the prefix
that `stateBeforeTime S rho t` folds. -/
private theorem index_lt_prefix_length (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time)
    {i : Nat} {e : NamedEvent V} (hi : rho.events[i]? = some e) (ht : e.time < t) :
    i < (rho.events.filter (fun f => decide (f.time < t))).length := by
  set p : NamedEvent V → Bool := fun f => decide (f.time < t) with hp
  set n := (rho.events.filter p).length with hn
  by_contra hcon
  have hge : n ≤ i := Nat.le_of_not_lt hcon
  have hfilt : rho.events.filter p = rho.events.take n :=
    filter_eq_take rho hsorted p (lt_downward t)
  have hdropnil : (rho.events.drop n).filter p = [] := by
    have h1 : rho.events.filter p =
        (rho.events.take n).filter p ++ (rho.events.drop n).filter p := by
      conv_lhs => rw [← List.take_append_drop n rho.events]
      rw [List.filter_append]
    have h2 : (rho.events.take n).filter p = rho.events.take n := by
      conv_lhs => rw [← hfilt]
      rw [List.filter_filter]
      simp only [Bool.and_self]
      exact hfilt
    rw [h2, ← hfilt] at h1
    exact List.self_eq_append_right.mp h1
  have hmem : e ∈ rho.events.drop n := by
    refine List.mem_of_getElem? (i := i - n) ?_
    rw [List.getElem?_drop]
    have hin : n + (i - n) = i := by omega
    rw [hin]
    exact hi
  have hin : e ∈ (rho.events.drop n).filter p :=
    List.mem_filter.mpr ⟨hmem, by simp only [hp, decide_eq_true_eq]; exact ht⟩
  rw [hdropnil] at hin
  simp at hin


omit [DecidableEq V] [Fintype V] in
/-- A sorted run's event times are monotone in the index. -/
theorem time_le_of_index_le (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {k m : Nat} {e f : NamedEvent V} (hk : rho.events[k]? = some e)
    (hm : rho.events[m]? = some f) (hkm : k ≤ m) : e.time ≤ f.time := by
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hml, hmf⟩ := List.getElem?_eq_some_iff.mp hm
  rcases Nat.eq_or_lt_of_le hkm with hEq | hlt
  · subst hEq
    rw [← hke, hmf]
  · have hp := (List.pairwise_iff_getElem.mp hsorted) k m hkl hml hlt
    rw [hke, hmf] at hp
    exact key_time_le hp

/-- The complete index bridge for a strict time read: `stateBeforeTime` at `t`
is a `stateBefore` prefix, and an event's index is inside that prefix exactly
when its time is strictly below `t`. -/
theorem stateBeforeTime_prefix_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    ∃ n : Nat, NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho n ∧
      (∀ (j : Nat) (e : NamedEvent V), j < n → rho.events[j]? = some e → e.time < t) ∧
      (∀ (j : Nat) (e : NamedEvent V), rho.events[j]? = some e → e.time < t → j < n) := by
  refine ⟨(rho.events.filter (fun f => decide (f.time < t))).length, ?_, ?_, ?_⟩
  · exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
      (filter_eq_take rho hsorted _ (lt_downward t))
  · intro j e hj he
    have hfilt := filter_eq_take rho hsorted (fun f => decide (f.time < t)) (lt_downward t)
    have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
      rw [hfilt]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2
  · intro j e he ht
    exact index_lt_prefix_length rho hsorted t he ht




omit [Fintype V] in
theorem update_finality_stable (st : Protocol.Store V) (sigma : ChainState V) :
    (Protocol.update_finality st sigma).latest_stable = st.latest_stable := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
theorem on_goldfish_vote_stable (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).latest_stable = st.latest_stable := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

theorem on_goldfish_vote_checked_stable (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).latest_stable = st.latest_stable := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_stable st u
  · rfl

theorem foldl_on_goldfish_vote_checked_stable (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).latest_stable = st.latest_stable := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih => rw [List.foldl_cons, ih, on_goldfish_vote_checked_stable]

omit [Fintype V] in
theorem on_sg_vote_stable (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).latest_stable = st.latest_stable := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

theorem on_block_using_stable (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_stable = st.latest_stable := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_stable, foldl_on_goldfish_vote_checked_stable]

omit [DecidableEq V] [Fintype V] in
theorem on_block_checked_using_stable (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_stable = st.latest_stable) :
    (Protocol.on_block_checked_using handle hc st B).latest_stable = st.latest_stable := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

omit [Fintype V] in
private theorem commitBlock_stable (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).core.latest_stable =
      after.latest_stable := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_stable (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_stable]
       exact on_block_checked_using_stable _ hc st.core B.erase
         (on_block_using_stable E st.core B.erase _))

omit [Fintype V] in
theorem admit_row_stable (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact on_sg_vote_stable hc st.core row.erase

omit [Fintype V] in
private theorem foldl_admit_row_stable (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).core.latest_stable =
      st.core.latest_stable := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_stable]

omit [Fintype V] in
theorem admit_rows_stable (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.latest_stable =
      st.core.latest_stable :=
  foldl_admit_row_stable hc rows st

omit [Fintype V] in
theorem admit_carried_stable (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).core.latest_stable =
      after.core.latest_stable := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_stable hc after B.attestations
      · rfl

theorem on_block_with_stable (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_stable]
  exact process_block_core_stable E hc cfg st B

theorem propose_block_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rfl
  | some B => exact on_block_with_stable .alsoCarried E hc cfg st B

theorem goldfish_vote_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1.latest_stable =
      st.latest_stable := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_stable E st _
  · rfl

theorem named_goldfish_vote_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact goldfish_vote_with_stable contract E hc nd st.core

theorem attest_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_stable hc st _

/-- Object receipt leaves the stable record unchanged. -/
theorem node_process_stable (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).st.core.latest_stable = n.st.core.latest_stable := by
  cases o with
  | block B => exact on_block_with_stable .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact on_goldfish_vote_checked_stable S.E n.st.core u
  | attest a => exact admit_row_stable S.hc n.st a

#print axioms process_block_core_stable
#print axioms propose_block_with_stable
#print axioms named_goldfish_vote_with_stable
#print axioms attest_with_stable
#print axioms node_process_stable

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
