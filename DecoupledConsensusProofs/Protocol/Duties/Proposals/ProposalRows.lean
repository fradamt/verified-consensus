module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusProofs.Protocol.Handlers.Admission
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Count

@[expose] public section

/-! Full-named source and identity regressions. Availability is
scoped to the selected window and enumerated/unique bodies; no global root
injectivity or actual named proposal/runtime is assumed. -/
namespace DecoupledConsensusModel.Proofs.NamedProposalRows
open Protocol.NamedProposalRows
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- Pool projection preserves full list order under the produced pool-view invariant. -/
theorem processed_rows_erasure (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (hPool : NamedStore.PoolView st) :
    (processedRows hc st).map NamedAttestation.erase = st.core.processed_attestations hc := by
  have key : ∀ rs : List Round,
      (rs.flatMap st.sg_rows).map NamedAttestation.erase = rs.flatMap st.core.sg_votes := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih => simp only [List.flatMap_cons, List.map_append, hPool r, ih]
  exact key _


theorem selected_source_exact (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) :
    select .poolAndCarried hc st = poolRows hc st ++ carriedRows hc st := rfl


theorem ordered_bodies_mem {st : Protocol.NamedStore V} {B : NamedBlock V}
    (hB : B ∈ orderedBodies st) : B ∈ st.bodies := by
  obtain ⟨root, _, hfind⟩ := List.mem_filterMap.mp hB
  exact Proofs.Engine.pickUnique?_mem hfind



/-- Carriage selection preserves the original row value, including its timeout entry. -/
theorem mem_carried_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    row ∈ carriedRows hc st ↔ ∃ B ∈ orderedBodies st,
      eligibleBody hc st B = true ∧ row ∈ B.attestations ∧
        Protocol.ProposalRows.inWindow hc st.core row.round = true := by
  simp only [carriedRows, List.mem_flatMap]
  constructor
  · rintro ⟨B, hB, hrow⟩
    by_cases he : eligibleBody hc st B = true
    · exact ⟨B, hB, he, by simpa [he] using hrow⟩
    · simp [he] at hrow
  · rintro ⟨B, hB, he, hrow⟩
    exact ⟨B, hB, by simpa [he] using hrow⟩


/-- On-chain exclusion compares full named rows, not SG projections or erasures. -/
theorem mem_exclude_on_chain (head : NamedBlock V) (rows : List (NamedAttestation V))
    (row : NamedAttestation V) :
    row ∈ excludeOnChain head rows ↔ row ∈ rows ∧ row ∉ chainRows head := by
  simp [excludeOnChain]

private theorem mem_cap_foldl (rows acc : List (NamedAttestation V))
    (row : NamedAttestation V)
    (h : row ∈ rows.foldl (fun kept next =>
      if next ∈ kept ||
          decide (2 ≤ (kept.filter (fun a =>
            decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
      then kept else kept ++ [next]) acc) : row ∈ acc ∨ row ∈ rows := by
  induction rows generalizing acc with
  | nil => exact Or.inl h
  | cons next rest ih =>
      simp only [List.foldl_cons] at h
      rcases ih _ h with hacc | hrest
      · split at hacc
        · exact Or.inl hacc
        · rcases List.mem_append.mp hacc with hacc | hnext
          · exact Or.inl hacc
          · refine Or.inr ?_
            simp only [List.mem_cons]
            exact Or.inl (by simpa using hnext)
      · exact Or.inr (by simp [hrest])

/-- Capping does not introduce a row. -/
theorem mem_capPerSigner (rows : List (NamedAttestation V))
    (row : NamedAttestation V) (h : row ∈ capPerSigner rows) : row ∈ rows := by
  exact (mem_cap_foldl rows [] row h).resolve_left (by simp)

private theorem mem_cap_foldl_of_unique
    (all remaining acc : List (NamedAttestation V)) (row : NamedAttestation V)
    (hacc : ∀ b ∈ acc, b ∈ all)
    (hremaining : ∀ b ∈ remaining, b ∈ all)
    (hunique : ∀ b ∈ all,
      b.val_index = row.val_index → b.round = row.round → b = row)
    (ha : row ∈ acc ∨ row ∈ remaining) :
    row ∈ remaining.foldl (fun kept next =>
      if next ∈ kept ||
          decide (2 ≤ (kept.filter (fun a =>
            decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
      then kept else kept ++ [next]) acc := by
  induction remaining generalizing acc with
  | nil =>
      rcases ha with h | h
      · exact h
      · simp at h
  | cons next tail ih =>
      let acc' : List (NamedAttestation V) :=
        if next ∈ acc ||
            decide (2 ≤ (acc.filter (fun a =>
              decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
        then acc else acc ++ [next]
      have hnext : next ∈ all := hremaining next (by simp)
      have hacc' : ∀ b ∈ acc', b ∈ all := by
        intro b hb
        dsimp [acc'] at hb
        split at hb
        · exact hacc b hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact hacc b hb
          · have hbeq : b = next := by simpa using hb
            rw [hbeq]
            exact hnext
      have htail : ∀ b ∈ tail, b ∈ all := by
        intro b hb
        exact hremaining b (by simp [hb])
      have ha' : row ∈ acc' ∨ row ∈ tail := by
        rcases ha with h | h
        · left
          dsimp [acc']
          split
          · exact h
          · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h | h
          · subst next
            left
            by_cases hm : row ∈ acc
            · dsimp [acc']
              split
              · exact hm
              · exact List.mem_append.mpr (Or.inl hm)
            · have hf : (acc.filter (fun b =>
                  decide (b.val_index = row.val_index ∧ b.round = row.round))) = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro b hb hkey
                have hkey' : b.val_index = row.val_index ∧ b.round = row.round :=
                  of_decide_eq_true hkey
                exact hm ((hunique b (hacc b hb) hkey'.1 hkey'.2) ▸ hb)
              have hguard : (decide (row ∈ acc) ||
                  decide (2 ≤ (acc.filter (fun b =>
                    decide (b.val_index = row.val_index ∧ b.round = row.round))).length)) =
                  false := by
                have hlim : ¬ 2 ≤ (acc.filter (fun b =>
                    decide (b.val_index = row.val_index ∧ b.round = row.round))).length := by
                  simp only [hf, List.length_nil]
                  decide
                exact Bool.or_eq_false_iff.mpr
                  ⟨decide_eq_false hm, decide_eq_false hlim⟩
              simp only [acc', hguard]
              simp
          · exact Or.inr h
      simpa only [List.foldl_cons] using ih acc' hacc' htail ha'

/-- A row unique among its signer and round survives the cap. -/
theorem mem_capPerSigner_of_unique (rows : List (NamedAttestation V))
    (row : NamedAttestation V) (hrow : row ∈ rows)
    (hunique : ∀ b ∈ rows,
      b.val_index = row.val_index → b.round = row.round → b = row) :
    row ∈ capPerSigner rows := by
  exact mem_cap_foldl_of_unique rows rows [] row (by simp)
    (fun _ h => h) hunique (Or.inr hrow)

private theorem cap_fold_count_le (rows acc : List (NamedAttestation V))
    (hacc : ∀ v : V, ∀ r : Round,
      (acc.filter (fun a => decide (a.val_index = v ∧ a.round = r))).length ≤ 2) :
    ∀ v : V, ∀ r : Round,
      ((rows.foldl (fun kept next =>
        if next ∈ kept ||
            decide (2 ≤ (kept.filter (fun a =>
              decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
        then kept else kept ++ [next]) acc).filter
          (fun a => decide (a.val_index = v ∧ a.round = r))).length ≤ 2 := by
  induction rows generalizing acc with
  | nil => exact hacc
  | cons next rest ih =>
      let acc' : List (NamedAttestation V) :=
        if next ∈ acc ||
            decide (2 ≤ (acc.filter (fun a =>
              decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
        then acc else acc ++ [next]
      have hacc' : ∀ v : V, ∀ r : Round,
          (acc'.filter (fun a => decide (a.val_index = v ∧ a.round = r))).length ≤ 2 := by
        intro v r
        by_cases hmem : next ∈ acc
        · have hguard : (decide (next ∈ acc) ||
                decide (2 ≤ (acc.filter (fun a =>
                  decide (a.val_index = next.val_index ∧ a.round = next.round))).length)) =
                true := Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hmem))
          simpa only [acc', hguard, if_true] using hacc v r
        · by_cases hlimit : 2 ≤ (acc.filter (fun a =>
              decide (a.val_index = next.val_index ∧ a.round = next.round))).length
          · have hguard : (decide (next ∈ acc) ||
                  decide (2 ≤ (acc.filter (fun a =>
                    decide (a.val_index = next.val_index ∧ a.round = next.round))).length)) =
                  true := Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true hlimit))
            simpa only [acc', hguard, if_true] using hacc v r
          · have hguard : (decide (next ∈ acc) ||
                decide (2 ≤ (acc.filter (fun a =>
                  decide (a.val_index = next.val_index ∧ a.round = next.round))).length)) =
                  false := Bool.or_eq_false_iff.mpr
                    ⟨decide_eq_false hmem, decide_eq_false hlimit⟩
            by_cases hkey : next.val_index = v ∧ next.round = r
            · rcases hkey with ⟨hv, hr⟩
              subst v
              subst r
              have hlt : (acc.filter (fun a =>
                  decide (a.val_index = next.val_index ∧ a.round = next.round))).length < 2 :=
                Nat.lt_of_not_ge hlimit
              simp only [acc', hguard]
              simpa [List.filter_append] using Nat.succ_le_of_lt hlt
            · have hsingle : ([next].filter (fun a =>
                  decide (a.val_index = v ∧ a.round = r))) = [] := by
                simp [hkey]
              simp only [acc', hguard]
              simp only [Bool.false_eq_true, if_false]
              rw [List.filter_append, hsingle]
              simpa using hacc v r
      simpa only [List.foldl_cons] using ih acc' hacc'

/-- The cap keeps at most two rows for each signer and round. -/
theorem capPerSigner_count_le (rows : List (NamedAttestation V))
    (v : V) (r : Round) :
    ((capPerSigner rows).filter
      (fun a => decide (a.val_index = v ∧ a.round = r))).length ≤ 2 := by
  exact cap_fold_count_le rows [] (by simp) v r

private theorem length_le_two_mul_keys {α β : Type} [DecidableEq β]
    (l : List α) (key : α → β)
    (h : ∀ b, (l.filter (fun a => decide (key a = b))).length ≤ 2) :
    l.length ≤ 2 * (l.map key).toFinset.card := by
  calc
    l.length = (l.map key).length := by simp
    _ = ∑ b ∈ (l.map key).toFinset, (l.map key).count b :=
      (List.sum_toFinset_count_eq_length _).symm
    _ ≤ ∑ b ∈ (l.map key).toFinset, 2 := by
      apply Finset.sum_le_sum
      intro b hb
      simpa [List.count, List.countP_map, Function.comp_def,
        List.countP_eq_length_filter, beq_iff_eq, List.filter_map] using h b
    _ = 2 * (l.map key).toFinset.card := by simp [mul_comm]

/-- The cap's length is at most twice the number of distinct signer and round
keys in its input. -/
theorem capPerSigner_length_le_keys (rows : List (NamedAttestation V)) :
    (capPerSigner rows).length ≤
      2 * (rows.map (fun a => (a.val_index, a.round))).toFinset.card := by
  let key : NamedAttestation V → V × Round := fun a => (a.val_index, a.round)
  have hcount : (capPerSigner rows).length ≤
      2 * ((capPerSigner rows).map key).toFinset.card := by
    apply length_le_two_mul_keys (capPerSigner rows) key
    intro ⟨v, r⟩
    simpa only [key, Prod.mk.injEq] using capPerSigner_count_le rows v r
  have hsubset : ((capPerSigner rows).map key).toFinset ⊆
      (rows.map key).toFinset := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨a, mem_capPerSigner rows a ha, rfl⟩
  exact hcount.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))

/-- A proposal row came from the selected source. -/
theorem mem_proposalRows (parent : NamedBlock V)
    (rows : List (NamedAttestation V)) (row : NamedAttestation V)
    (h : row ∈ proposalRows parent rows) :
    row ∈ rows ∧ row ∉ chainRows parent := by
  exact (mem_exclude_on_chain parent rows row).mp (mem_capPerSigner _ _ h)

/-- A selected row with a unique signer and round survives when it is not
already carried on the parent chain. -/
theorem mem_proposalRows_of_unique (parent : NamedBlock V)
    (rows : List (NamedAttestation V)) (row : NamedAttestation V)
    (hrow : row ∈ rows) (hoff : row ∉ chainRows parent)
    (hunique : ∀ b ∈ rows,
      b.val_index = row.val_index → b.round = row.round → b = row) :
    row ∈ proposalRows parent rows := by
  apply mem_capPerSigner_of_unique
  · exact (mem_exclude_on_chain parent rows row).mpr ⟨hrow, hoff⟩
  · intro b hb hval hround
    have hsource := (mem_exclude_on_chain parent rows b).mp hb
    exact hunique b hsource.1 hval hround




#print axioms processed_rows_erasure
#print axioms selected_source_exact
#print axioms ordered_bodies_mem
#print axioms mem_carried_rows
#print axioms mem_exclude_on_chain
#print axioms mem_capPerSigner
#print axioms mem_capPerSigner_of_unique
#print axioms capPerSigner_count_le
#print axioms capPerSigner_length_le_keys
#print axioms mem_proposalRows
#print axioms mem_proposalRows_of_unique
end DecoupledConsensusModel.Proofs.NamedProposalRows

end
