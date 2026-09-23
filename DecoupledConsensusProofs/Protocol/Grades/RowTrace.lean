module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Bucket rounds: copied from the private block of `NamedRawSource` -/

/-- Copied from `NamedRawSource`. -/
private def RowsOwn (st : Protocol.NamedStore V) : Prop :=
  ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k → a.round = k

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem row_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming : NamedAttestation V) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.admit_row hc st incoming) := by
  intro k a ha
  rcases row_mem_cases_at hc st incoming a k ha with hold | ⟨rfl, rfl⟩
  · exact h k a hold
  · rfl

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem rows_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_own hc st a h)

/-- Copied from `NamedRawSource`. -/
private theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

/-- Copied from `NamedRawSource`. -/
private theorem block_own (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : RowsOwn st) :
    RowsOwn (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hc : RowsOwn (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) := by
    simpa only [RowsOwn, core_block_rows] using h
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_own S.hc _ B.attestations hc
  · exact hc

/-- Copied from `NamedRawSource`. -/
private theorem propose_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_own S st _ h

/-- Copied from `NamedRawSource`. -/
private theorem tick_preserves_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (t : Time) (P : Protocol.NamedStore V → Prop)
    (hclock : ∀ st, P st → P (Protocol.NamedStore.setClock S.E st t))
    (hprop : ∀ st, P st →
      P (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1)
    (hgf : ∀ st, P st →
      P (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1)
    (hconf : ∀ st s, P st →
      P (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s))
    (hatt : ∀ st record, P st →
      P (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (h : P st) :
    P (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> solve_by_elim (maxDepth := 10) [hclock, hprop, hgf, hconf, hatt]

/-- Copied from `NamedRawSource`. -/
private theorem tick_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (h : RowsOwn st) :
    RowsOwn (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  have hclock : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedStore.setClock S.E st t) := fun _ hs => hs
  have hprop : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 :=
    propose_own gc S nd
  have hgf : ∀ st, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := fun _ hs => hs
  have hconf : ∀ st s, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) := fun _ _ hs => hs
  have hatt : ∀ st record, RowsOwn st →
      RowsOwn (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
    fun st record hs => row_own S.hc st _ hs
  exact tick_preserves_own gc S nd t RowsOwn hclock hprop hgf hconf hatt st record h

/-- Copied from `NamedRawSource`. -/
private theorem process_own (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V)
    (h : RowsOwn st) : RowsOwn (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_own S st B h
  | gfVote u => exact h
  | attest a => exact row_own S.hc st a h

/-- Copied from `NamedRawSource`. -/
private theorem own_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (reader : V) :
    RowsOwn (NamedRun.stateBefore S rho i reader).st := by
  induction i with
  | zero =>
    intro k a ha
    simp only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, List.not_mem_nil] at ha
  | succ i ih =>
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => exact ih
    | some e =>
      change RowsOwn (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
      by_cases hv : reader = e.node
      · cases e with
        | tick v t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_tick]
          exact tick_own _ S (S.node reader) _ _ t ih
        | deliver v o t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_deliver]
          exact process_own S _ o ih
      · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
        exact ih

/-- Copied from `NamedRawSource`, and the export the L6 report asked for:
a held row sits in its own bucket at **any** strict read, not only at a phase
cutoff. -/
theorem own_strict_read (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (read : Time) (reader : V) :
    ∀ k (a : NamedAttestation V),
      a ∈ (NamedRun.stateBeforeTime S rho read reader).st.sg_rows k → a.round = k := by
  obtain ⟨n, hn, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  rw [hn]
  exact own_stateBefore S rho n reader

/-! ## Strict-read prefix helpers: copied from `NamedHealthyHeadReady` -/

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

/-- Copied from `NamedHealthyHeadReady`. -/
theorem strict_read_eq_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (strict_filter_eq_take rho hsorted t)

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
theorem strict_lengths_mono (rho : NamedRun V) {early late : Time} (ht : early ≤ late) :
    (rho.events.filter (fun e => decide (e.time < early))).length ≤
      (rho.events.filter (fun e => decide (e.time < late))).length := by
  have hsub := List.Sublist.filter (fun e : NamedEvent V => decide (e.time < late))
    (List.filter_sublist (p := fun e : NamedEvent V => decide (e.time < early)) (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < early))).filter
      (fun e => decide (e.time < late)) = rho.events.filter (fun e => decide (e.time < early)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hearly : e.time < early := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hearly.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

/-- Time-monotone carry of a held SG row and its projection stamp between two
strict reads. Assembled from the public `stateBefore_sg_row_stamp_mono` and the
prefix helpers above. -/
theorem strict_sg_row_carry (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d)
    {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBeforeTime S rho c reader).st.sg_rows a.round) :
    a ∈ (NamedRun.stateBeforeTime S rho d reader).st.sg_rows a.round ∧
      (NamedRun.stateBeforeTime S rho d reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase) =
        (NamedRun.stateBeforeTime S rho c reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase) := by
  rw [strict_read_eq_index S rho sch.sorted c] at ha
  rw [strict_read_eq_index S rho sch.sorted c, strict_read_eq_index S rho sch.sorted d]
  exact Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader
    (strict_lengths_mono rho hcd) ha

/-- Copied from `NamedHealthyHeadReady`. -/
theorem held_find_at_strict (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (roots : NamedRootCollisionFree S rho)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T H.erase.root =
      some H.erase := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH ⊢
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n reader).1.1.1
  have hHscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)
  have hHraw : H.erase ∈ (NamedRun.stateBefore S rho n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
  intro raw hraw hroot
  rw [hcoh.1] at hraw
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hraw
  have hotherScope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hother)
  have hroots : other.root = H.root :=
    (Proofs.NamedWire.erase_root other).symm.trans (hroot.trans (Proofs.NamedWire.erase_root H))
  have hself : ∀ B : NamedBlock V, NamedBlock.Preceq B B := by
    intro B; cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]
  exact congrArg NamedBlock.erase (roots.root_injective other H hotherScope hHscope other H
    (Or.inl (hself other)) (Or.inr (hself H)) hroots)

/-! ## The traceback -/

/-- An SG token in the bucketed pool at a strict read comes from an original
full row held at that read, in its own bucket. -/
theorem pool_token_row (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V)
    {k : Round} {x : Protocol.SGVote V}
    (hx : x ∈
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView.sg_votes k) :
    ∃ a : NamedAttestation V, a.round = k ∧ Protocol.sgVote a.erase = x ∧
      a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round := by
  let n := NamedRun.stateBeforeTime S rho cut reader
  change x ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hx
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hx
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := own_strict_read S rho sch cut reader k a ha
  exact ⟨a, hround, (congrArg Protocol.sgVote herase).trans hproj,
    by simpa only [hround] using ha⟩

/-- An honest sender's row held at a strict read was emitted at that round's
action, strictly before the read. The shape of
`NamedOutageProvenance.honest_held_ancestor_row_before_action`, at a general
cut and for a directly held row. -/
theorem honest_held_row_before_cut (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut : Time) (reader : V) {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round)
    (hHon : a.val_index ∈ rho.honest) :
    S.a a.round < cut ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨i, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread] at ha
  obtain ⟨j, hj, t, hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_row_emission S rho auth i reader ha hHon
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have ht : t < cut := by simpa only [het] using hbefore j e hj he
  exact ⟨lt_of_le_of_lt hsend ht, hem⟩

#print axioms own_strict_read
#print axioms strict_sg_row_carry
#print axioms pool_token_row
#print axioms honest_held_row_before_cut

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
