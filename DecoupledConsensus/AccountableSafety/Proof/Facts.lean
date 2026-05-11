import DecoupledConsensus.AccountableSafety.Model.Certificates

namespace AccountableSafety

/-! # Accountable Safety Proofs: basic facts

Arithmetic, selector, block-geometry, field-preservation, height progression,
and chain-shape facts used by the invariant and safety layers. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

lemma isQuorumStrictBool_eq_true_iff (Q : Finset (Validator n)) :
    isQuorumStrictBool n Q = true ↔ IsQuorumStrict n Q := by
  unfold isQuorumStrictBool IsQuorumStrict
  rw [Nat.ble_eq]

/-- The two forms agree under the BFT convention `n = 3 * f + 1`. -/
lemma isQuorum_iff_strict {f : ℕ} (hn : n = 3 * f + 1)
    (Q : Finset (Validator n)) : IsQuorum f Q ↔ IsQuorumStrict n Q := by
  unfold IsQuorum IsQuorumStrict
  omega

/-- Inclusion-exclusion for finsets of validators. -/
lemma quorum_inclusion_exclusion (Q Q' : Finset (Validator n)) :
    (Q ∩ Q').card + n ≥ Q.card + Q'.card := by
  have h_union_inter : (Q ∪ Q').card + (Q ∩ Q').card = Q.card + Q'.card :=
    Finset.card_union_add_card_inter Q Q'
  have h_union_le : (Q ∪ Q').card ≤ n := by
    have h := Finset.card_le_univ (Q ∪ Q')
    simpa using h
  omega

/-- **Quorum intersection** in the strict 2/3 convention: any two quorums
    share at least `(n + 2)/3` validators. Stated in `IsQuorumStrict` form
    for use by the state-machine lemmas; the BFT-form analogue (sharing
    at least `f + 1` validators when `n = 3 * f + 1`) is `quorum_intersection_f`
    below. -/
lemma quorum_intersection (Q Q' : Finset (Validator n))
    (hQ : IsQuorumStrict n Q) (hQ' : IsQuorumStrict n Q') :
    3 * (Q ∩ Q').card ≥ n + 2 := by
  have h := quorum_inclusion_exclusion Q Q'
  unfold IsQuorumStrict at hQ hQ'
  omega

/-- **Quorum intersection** in the BFT convention `n = 3 * f + 1`:
    any two literal-form quorums (each of size `≥ 2 * f + 1`) share at
    least `f + 1` validators. -/
lemma quorum_intersection_f {f : ℕ} (hn : n = 3 * f + 1)
    (Q Q' : Finset (Validator n))
    (hQ : IsQuorum f Q) (hQ' : IsQuorum f Q') :
    (Q ∩ Q').card ≥ f + 1 := by
  have h := quorum_inclusion_exclusion Q Q'
  unfold IsQuorum at hQ hQ'
  omega

namespace Block

/-- A successful lookup returns a block whose id is the queried id. This does
    not require global id injectivity. -/
lemma findById_id {root T : Block n} {bid : BlockId}
    (h : findById root bid = some T) : T.id = bid := by
  induction root with
  | genesis =>
      unfold findById at h
      by_cases hb : bid = 0
      · simp [hb] at h
        cases h
        simp [id, hb]
      · simp [hb] at h
  | mk selfId parent s vs ih =>
      unfold findById at h
      by_cases hb : bid = selfId
      · simp [hb] at h
        cases h
        simp [id, hb]
      · simp [hb] at h
        exact ih h

/-- A successful lookup returns a parent-pointer ancestor of the lookup root.
    Slot-order consequences require a separate `root.WellFormed` premise. -/
lemma findById_ancestor {root T : Block n} {bid : BlockId}
    (h : findById root bid = some T) : T ≼ root := by
  induction root with
  | genesis =>
      unfold findById at h
      by_cases hb : bid = 0
      · simp [hb] at h
        cases h
        exact .refl _
      · simp [hb] at h
  | mk selfId parent s vs ih =>
      unfold findById at h
      by_cases hb : bid = selfId
      · simp [hb] at h
        cases h
        exact .refl _
      · simp [hb] at h
        exact .step (ih h)

/-- Transitivity of the ancestor relation. -/
lemma Ancestor.trans {A B C : Block n} (h1 : A ≼ B) (h2 : B ≼ C) : A ≼ C := by
  induction h2 with
  | refl      => exact h1
  | step _ ih => exact .step ih

/-- A block is a parent-pointer ancestor of any raw child whose parent is that
    block. There is intentionally no `B.slot < s` premise here; well-formedness
    is tracked separately. -/
lemma Ancestor.step_self (B : Block n) (bid s : ℕ) (vs : List (Vote n)) :
    B ≼ Block.mk bid B s vs :=
  .step (.refl B)

/-- Any two parent-pointer ancestors of a common block are comparable. This is
    a structural fact about a single parent chain and does not need slots. -/
lemma Ancestor.linear {Z : Block n} : ∀ {X Y : Block n}, X ≼ Z → Y ≼ Z → X ≼ Y ∨ Y ≼ X := by
  intro X Y hX hY
  induction Z with
  | genesis =>
    cases hX; cases hY; left; exact .refl _
  | mk selfId Z' s vs ihZ =>
    cases hX with
    | refl => right; exact hY
    | step hX' =>
      cases hY with
      | refl => left; exact hX'.step
      | step hY' => exact ihZ hX' hY'

/-- A parent-pointer ancestor of a well-formed block is well-formed. -/
lemma Ancestor.wellformed_of {X Y : Block n} (h : X ≼ Y) (hWF : WellFormed Y) : WellFormed X := by
  induction h with
  | refl => exact hWF
  | step _ ih => exact ih hWF.2

/-- For a well-formed block, slots are non-decreasing along parent-pointer
    ancestry. This is where the separated slot-validity condition is used. -/
lemma Ancestor.slot_le {X Y : Block n} (h : X ≼ Y) (hWF : WellFormed Y) : X.slot ≤ Y.slot := by
  induction h with
  | refl => exact le_refl _
  | step h' ih =>
    rename_i C bid s vs
    have hWFC : WellFormed C := hWF.2
    have hslot : C.slot < s := hWF.1
    have ihX : X.slot ≤ C.slot := ih hWFC
    show X.slot ≤ s; omega

/-- For ancestors of a common well-formed tip, slot order determines ancestor
    order. The common `hWF` premise rules out malformed equal/decreasing-slot
    parent links. -/
lemma Ancestor.le_of_slot_le {Z : Block n} (hWF : WellFormed Z) {X Y : Block n}
    (hX : X ≼ Z) (hY : Y ≼ Z) (hslot : X.slot ≤ Y.slot) : X ≼ Y := by
  rcases Ancestor.linear hX hY with h | h
  · exact h
  · have hWFX : WellFormed X := hX.wellformed_of hWF
    have hYX : Y.slot ≤ X.slot := h.slot_le hWFX
    have hEq : X.slot = Y.slot := le_antisymm hslot hYX
    cases h with
    | refl => exact .refl _
    | step h' =>
      rename_i X_par bid s vs
      exfalso
      have h1 : Y.slot ≤ X_par.slot := h'.slot_le hWFX.2
      have h2 : (Block.mk bid X_par s vs).slot = s := rfl
      have h3 : X_par.slot < s := hWFX.1
      omega

/-- Parent-pointer ancestry is antisymmetric on well-formed chains. Without
    well-formedness, malformed cycles are still impossible by the inductive
    structure, but slot-based proof obligations would be unavailable. -/
lemma Ancestor.antisymm {X Y : Block n} (hXY : X ≼ Y) (hYX : Y ≼ X)
    (hWFY : WellFormed Y) : X = Y := by
  have hWFX : WellFormed X := hXY.wellformed_of hWFY
  have hXY_slot : X.slot ≤ Y.slot := hXY.slot_le hWFY
  have hYX_slot : Y.slot ≤ X.slot := hYX.slot_le hWFX
  have hslot : X.slot = Y.slot := le_antisymm hXY_slot hYX_slot
  cases hXY with
  | refl => rfl
  | step h' =>
    rename_i C bid s vs
    exfalso
    have h1 : X.slot ≤ C.slot := h'.slot_le hWFY.2
    have h2 : C.slot < s := hWFY.1
    have h3 : (Block.mk bid C s vs).slot = s := rfl
    omega

end Block

lemma justifiedBool_eq_true_iff (σ : State n) (T : Block n) :
    justifiedBool σ T = true ↔ Justified σ T := by
  unfold justifiedBool Justified
  exact isQuorumStrictBool_eq_true_iff _

lemma timeoutFiresBool_eq_true_iff (σ : State n) :
    timeoutFiresBool σ = true ↔ TimeoutFires σ := by
  unfold timeoutFiresBool TimeoutFires
  exact isQuorumStrictBool_eq_true_iff _

lemma currentlyFinalBool_eq_true_iff (σ : State n) :
    currentlyFinalBool σ = true ↔ CurrentlyFinal σ := by
  unfold currentlyFinalBool CurrentlyFinal
  exact isQuorumStrictBool_eq_true_iff _

/-! ### Deterministic justified-target selection -/

private lemma List.findSome?_some_mem {α β : Type} {f : α → Option β} {l : List α} {b : β}
    (h : l.findSome? f = some b) : ∃ a ∈ l, f a = some b := by
  induction l with
  | nil =>
      simp at h
  | cons a as ih =>
      simp [List.findSome?] at h
      cases hfa : f a with
      | none =>
          simp [hfa] at h
          obtain ⟨a', hm, hf⟩ := ih h
          exact ⟨a', by simp [hm], hf⟩
      | some b' =>
          simp [hfa] at h
          cases h
          exact ⟨a, by simp, hfa⟩

private lemma List.findSome?_exists_of_mem {α β : Type} {f : α → Option β} {l : List α}
    {a : α} {b : β} (ha : a ∈ l) (hf : f a = some b) :
    ∃ b', l.findSome? f = some b' := by
  induction l with
  | nil =>
      simp at ha
  | cons x xs ih =>
      simp at ha
      cases hfx : f x with
      | some b' =>
          refine ⟨b', ?_⟩
          simp [List.findSome?, hfx]
      | none =>
          rcases ha with hax | ha
          · subst hax
            simp [hfx] at hf
          · obtain ⟨b', hb'⟩ := ih ha
            refine ⟨b', ?_⟩
            simp [List.findSome?, hfx, hb']

/-- If a block is justified, at least one validator's current target is that
    block. This lets the executable selector below search validator targets
    rather than the infinite block type. -/
lemma justified_extract_witness {σ : State n} {T : Block n} (hJ : Justified σ T) :
    ∃ i, σ.targets i = some T := by
  unfold Justified IsQuorumStrict at hJ
  have h_pos : 0 < (targetedSet σ T).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h_pos
  refine ⟨i, ?_⟩
  unfold targetedSet at hi
  simp [Finset.mem_filter] at hi
  exact hi

lemma firstJustifiedTarget_sound {σ : State n} {T : Block n}
    (h : firstJustifiedTarget σ = some T) : Justified σ T := by
  unfold firstJustifiedTarget at h
  obtain ⟨i, _, hi⟩ := List.findSome?_some_mem h
  cases htarget : σ.targets i with
  | none =>
      simp [htarget] at hi
  | some Tsel =>
      by_cases hJ : justifiedBool σ Tsel = true
      · simp [htarget, hJ] at hi
        cases hi
        exact (justifiedBool_eq_true_iff σ T).mp hJ
      · simp [htarget, hJ] at hi

lemma firstJustifiedTarget_complete {σ : State n}
    (h : ∃ T, Justified σ T) : ∃ T, firstJustifiedTarget σ = some T := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨i, hi⟩ := justified_extract_witness hT
  unfold firstJustifiedTarget
  exact List.findSome?_exists_of_mem
    (f := fun i =>
      match σ.targets i with
      | none => none
      | some T => if justifiedBool σ T then some T else none)
    (a := i) (b := T) (List.mem_finRange i)
    (by simp [hi, (justifiedBool_eq_true_iff σ T).mpr hT])

lemma firstJustifiedTarget_eq_none_iff (σ : State n) :
    firstJustifiedTarget σ = none ↔ ¬ ∃ T, Justified σ T := by
  constructor
  · intro hnone h_exists
    obtain ⟨T, hsome⟩ := firstJustifiedTarget_complete h_exists
    rw [hnone] at hsome
    cases hsome
  · intro hnot
    cases hfirst : firstJustifiedTarget σ with
    | none => rfl
    | some T =>
        exact False.elim (hnot ⟨T, firstJustifiedTarget_sound hfirst⟩)

/-! ### Helper lemmas about `applyFinality`

`applyFinality` only mutates the `F` field. All other fields are preserved. -/

@[simp] lemma applyFinality_s (σ : State n) : (applyFinality σ).s = σ.s := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_h (σ : State n) : (applyFinality σ).h = σ.h := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_targets (σ : State n) :
    (applyFinality σ).targets = σ.targets := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_timeouts (σ : State n) :
    (applyFinality σ).timeouts = σ.timeouts := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_J (σ : State n) : (applyFinality σ).J = σ.J := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_hj (σ : State n) : (applyFinality σ).hj = σ.hj := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_sh (σ : State n) : (applyFinality σ).sh = σ.sh := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_L (σ : State n) : (applyFinality σ).L = σ.L := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_P (σ : State n) : (applyFinality σ).P = σ.P := by
  unfold applyFinality; split_ifs <;> rfl

@[simp] lemma applyFinality_Justified (σ : State n) (T : Block n) :
    Justified (applyFinality σ) T ↔ Justified σ T := by
  simp [Justified, targetedSet]

@[simp] lemma applyFinality_TimeoutFires (σ : State n) :
    TimeoutFires (applyFinality σ) ↔ TimeoutFires σ := by
  simp [TimeoutFires, timedOutSet]


/-! ### Field-preservation lemmas for `processVote`

`processVote` only mutates `targets`, `timeouts`, and (possibly) `P`.
Every other field is preserved. -/

/-! Field-preservation lemmas for `processVoteCore` (no nested ifs — clean). -/

@[simp] lemma processVoteCore_h (σ : State n) (v : Vote n) :
    (processVoteCore σ v).h = σ.h := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_hj (σ : State n) (v : Vote n) :
    (processVoteCore σ v).hj = σ.hj := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_sh (σ : State n) (v : Vote n) :
    (processVoteCore σ v).sh = σ.sh := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_J (σ : State n) (v : Vote n) :
    (processVoteCore σ v).J = σ.J := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_F (σ : State n) (v : Vote n) :
    (processVoteCore σ v).F = σ.F := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_L (σ : State n) (v : Vote n) :
    (processVoteCore σ v).L = σ.L := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_s (σ : State n) (v : Vote n) :
    (processVoteCore σ v).s = σ.s := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

@[simp] lemma processVoteCore_P (σ : State n) (v : Vote n) :
    (processVoteCore σ v).P = σ.P := by
  unfold processVoteCore
  split
  · split_ifs <;> rfl
  · split
    · rfl
    · split_ifs <;> rfl

/-! Field-preservation lemmas for `processVote` (composition with the P-update). -/

/-- Helper: write `processVote` in inlined if-then-else form (no `let`). -/
lemma processVote_eq_ite (σ : State n) (v : Vote n) :
    processVote σ v =
      (if v.finalize = some ((processVoteCore σ v).hj, (processVoteCore σ v).J.id) then
        { (processVoteCore σ v) with P := insert v.validator (processVoteCore σ v).P }
       else processVoteCore σ v) := rfl

@[simp] lemma processVote_h (σ : State n) (v : Vote n) :
    (processVote σ v).h = σ.h := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_hj (σ : State n) (v : Vote n) :
    (processVote σ v).hj = σ.hj := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_sh (σ : State n) (v : Vote n) :
    (processVote σ v).sh = σ.sh := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_J (σ : State n) (v : Vote n) :
    (processVote σ v).J = σ.J := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_F (σ : State n) (v : Vote n) :
    (processVote σ v).F = σ.F := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_L (σ : State n) (v : Vote n) :
    (processVote σ v).L = σ.L := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_s (σ : State n) (v : Vote n) :
    (processVote σ v).s = σ.s := by
  rw [processVote_eq_ite]; split_ifs <;> simp

@[simp] lemma processVote_targets (σ : State n) (v : Vote n) :
    (processVote σ v).targets = (processVoteCore σ v).targets := by
  rw [processVote_eq_ite]; split_ifs <;> rfl

@[simp] lemma processVote_timeouts (σ : State n) (v : Vote n) :
    (processVote σ v).timeouts = (processVoteCore σ v).timeouts := by
  rw [processVote_eq_ite]; split_ifs <;> rfl

/-! ### Characterization of `processVoteCore.targets`

Either the targets array is unchanged at index `i`, or this `processVote`
fired the freshness branch, set `targets[v.validator] := some T`, and
gave us all the freshness witnesses. This is the key lemma for proving
the `targets`-related invariants. -/

lemma processVoteCore_targets_eq_cases (σ : State n) (v : Vote n) (i : Validator n) :
    (processVoteCore σ v).targets i = σ.targets i ∨
    (i = v.validator ∧ ∃ T, v.target = some T.id ∧ v.height = σ.h ∧
        T ≼ σ.L ∧ T.slot ≥ σ.sh ∧ (processVoteCore σ v).targets i = some T) := by
  match h_target : v.target with
  | none =>
    -- v.target = none: only the timeouts may update; targets untouched.
    left
    simp [processVoteCore, h_target]
    split_ifs <;> rfl
  | some bid =>
    -- v.target names a block id. It updates targets only if the id resolves
    -- on the current chain and satisfies the height/slot freshness check.
    match h_find : σ.L.findById bid with
    | none =>
      left
      simp [processVoteCore, h_target, h_find]
    | some T_v =>
      by_cases h_fresh : v.height = σ.h ∧ T_v.slot ≥ σ.sh
      · by_cases hi : i = v.validator
        · -- i = v.validator: targets i = some T_v, with id-resolution witnesses.
          right
          refine ⟨hi, T_v, ?_, h_fresh.1, Block.findById_ancestor h_find,
            h_fresh.2, ?_⟩
          · rw [← Block.findById_id h_find]
          · subst hi
            simp [processVoteCore, h_target, h_find, h_fresh]
        · -- i ≠ v.validator: targets unchanged at i.
          left
          simp [processVoteCore, h_target, h_find, h_fresh, Function.update, hi]
      · -- Not fresh: σ'.targets unchanged.
        left
        simp [processVoteCore, h_target, h_find, h_fresh]

/-! ### Field-preservation lemmas for `processBlock`

`processBlock σ B = B.votes.foldl processVote { σ with L := B }`.
The fold applies `processVote` repeatedly; each application preserves the
fields above. The outer `{ σ with L := B }` overwrites only `L`. -/

@[simp] lemma processBlock_h (σ : State n) (B : Block n) :
    (processBlock σ B).h = σ.h := by
  unfold processBlock
  -- Induction on the fold: prove the property is invariant under each step.
  suffices ∀ τ : State n, τ.h = σ.h → (B.votes.foldl processVote τ).h = σ.h by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

@[simp] lemma processBlock_s (σ : State n) (B : Block n) :
    (processBlock σ B).s = σ.s := by
  unfold processBlock
  suffices ∀ τ : State n, τ.s = σ.s → (B.votes.foldl processVote τ).s = σ.s by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

@[simp] lemma processBlock_hj (σ : State n) (B : Block n) :
    (processBlock σ B).hj = σ.hj := by
  unfold processBlock
  suffices ∀ τ : State n, τ.hj = σ.hj → (B.votes.foldl processVote τ).hj = σ.hj by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

@[simp] lemma processBlock_sh (σ : State n) (B : Block n) :
    (processBlock σ B).sh = σ.sh := by
  unfold processBlock
  suffices ∀ τ : State n, τ.sh = σ.sh → (B.votes.foldl processVote τ).sh = σ.sh by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

@[simp] lemma processBlock_J (σ : State n) (B : Block n) :
    (processBlock σ B).J = σ.J := by
  unfold processBlock
  suffices ∀ τ : State n, τ.J = σ.J → (B.votes.foldl processVote τ).J = σ.J by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

@[simp] lemma processBlock_F (σ : State n) (B : Block n) :
    (processBlock σ B).F = σ.F := by
  unfold processBlock
  suffices ∀ τ : State n, τ.F = σ.F → (B.votes.foldl processVote τ).F = σ.F by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

-- (Monotonicity helpers `processHeight_*` and `processSlot_*` are below,
-- after `height_progression` which they depend on.)

/-! # Section 2: Accountable Safety
    Lemmas 1–4 and the main theorem. -/

/-- **Lemma 1 (Height progression).**
    `processHeight` increments `h` by 0 or 1 per invocation, and any increment
    is gated by a `≥ 2n/3` justification or timeout quorum (witnessed in the
    *pre-state* `σ`, since the height-advance branches reset `targets`/`timeouts`).

    Note: stated about pre-state `σ` because the post-state `σ'` clears the
    target/timeout arrays as part of the advance. -/
lemma height_progression (σ : State n) :
    ((processHeight σ).h = σ.h ∨ (processHeight σ).h = σ.h + 1) ∧
    ((processHeight σ).h = σ.h + 1 →
      (∃ T, Justified σ T) ∨ TimeoutFires σ) := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    -- Justification branch: h advances by 1, with the selected target as witness.
    simp [hFirst]
    exact Or.inl ⟨T, by simpa using firstJustifiedTarget_sound hFirst⟩
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- Timeout branch: h advances by 1, witness is TimeoutFires σ.
      simp [hFirst, hTO]
      exact Or.inr (by simpa using (timeoutFiresBool_eq_true_iff (applyFinality σ)).mp hTO)
    | false =>
      -- Neither branch fires: σ' = applyFinality σ, so h unchanged.
      simp [hFirst, hTO]

/-! ### Monotonicity helpers derived from `height_progression`. -/

/-- `processHeight` does not decrease `h`. -/
lemma processHeight_h_le (σ : State n) : σ.h ≤ (processHeight σ).h := by
  rcases (height_progression σ).1 with h | h
  · exact h.symm.le
  · rw [h]; omega

/-- `processHeight` does not change `s`. -/
@[simp] lemma processHeight_s (σ : State n) : (processHeight σ).s = σ.s := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO]

/-- `processSlot` increments `s` by 1. -/
lemma processSlot_s_eq (σ : State n) : (processSlot σ).s = σ.s + 1 := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simp [processSlot, hEmpty]
  · simp [processSlot, hEmpty]

@[simp] lemma processSlot_F (σ : State n) :
    (processSlot σ).F =
      if σ.L.slot < σ.s then (processHeight σ).F else σ.F := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simp [processSlot, hEmpty]
  · simp [processSlot, hEmpty]

/-- `processSlot` does not decrease `h`. -/
lemma processSlot_h_le (σ : State n) : σ.h ≤ (processSlot σ).h := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_h_le σ
  · simp [processSlot, hEmpty]

/-! ### Partial Lemma 2 (Checkpoint monotonicity)

The full Lemma 2 of the paper has seven conjuncts: `s, h, hj, sh` non-decreasing,
plus `F ≼ F'`, `J ≼ J'`, `F' ≼ J'`. We prove the two "easy" parts here
(`s` and `h`) as standalone lemmas. The other five conjuncts require:

  - For `hj`: maintaining the invariant `hj ≤ h` (then hj only changes when
    justification fires, setting hj ← h, which preserves the monotonicity).
  - For `sh`: requires slot-monotonicity along `≼` plus the state-height
    boundary machinery from the paper.
  - For `F, J` along `≼`: requires the freshness machinery. We prove the
    chain-extension form used by safety (`chain_J_monotone_step`), rather
    than the paper's full all-conjunct Lemma 2 as one theorem. -/

/-- `s` is non-decreasing across one `stateTransition`. -/
lemma stateTransition_s_le (σ : State n) (B : Block n) :
    σ.s ≤ (stateTransition σ B).s := by
  unfold stateTransition
  rw [processHeight_s, processBlock_s]
  -- Now goal: σ.s ≤ (iterateProcessSlot σ (B.slot - σ.s)).s
  -- Each iteration bumps s by 1, so s ≤ s + k.
  generalize B.slot - σ.s = k
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]
  | succ k ih =>
    show σ.s ≤ (iterateProcessSlot (processSlot σ) k).s
    have h1 : σ.s ≤ (processSlot σ).s := by rw [processSlot_s_eq]; omega
    exact h1.trans (ih _)

/-- `h` is non-decreasing across one `stateTransition`. -/
lemma stateTransition_h_le (σ : State n) (B : Block n) :
    σ.h ≤ (stateTransition σ B).h := by
  unfold stateTransition
  apply le_trans ?_ (processHeight_h_le _)
  rw [processBlock_h]
  generalize B.slot - σ.s = k
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]
  | succ k ih =>
    show σ.h ≤ (iterateProcessSlot (processSlot σ) k).h
    exact (processSlot_h_le σ).trans (ih _)

/-! ### Additional field-preservation lemmas for `processHeight`, `processSlot`, `processBlock` -/

@[simp] lemma processHeight_L (σ : State n) : (processHeight σ).L = σ.L := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO]

@[simp] lemma processSlot_L (σ : State n) : (processSlot σ).L = σ.L := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simp [processSlot, hEmpty]
  · simp [processSlot, hEmpty]

@[simp] lemma processBlock_L (σ : State n) (B : Block n) :
    (processBlock σ B).L = B := by
  unfold processBlock
  suffices ∀ τ : State n, τ.L = B → (B.votes.foldl processVote τ).L = B by
    exact this _ rfl
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [hτ])

/-! ### Lemmas about `iterateProcessSlot` -/

@[simp] lemma iterateProcessSlot_L (σ : State n) (k : ℕ) :
    (iterateProcessSlot σ k).L = σ.L := by
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]
  | succ k ih =>
    show (iterateProcessSlot (processSlot σ) k).L = σ.L
    rw [ih]; simp

lemma iterateProcessSlot_s_eq (σ : State n) (k : ℕ) :
    (iterateProcessSlot σ k).s = σ.s + k := by
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]
  | succ k ih =>
    show (iterateProcessSlot (processSlot σ) k).s = σ.s + (k + 1)
    rw [ih, processSlot_s_eq]; omega

/-! ### Chain tip-shape lemmas -/

/-- The `L` field of a chain's tip-state equals the tip block. -/
@[simp] lemma chain_state_L_eq_tip {B : Block n} (chain : Chain n B) :
    (stateOf chain).L = B := by
  induction chain with
  | genesis => simp [stateOf, State.genesis]
  | extend c bid newSlot votes hSlot ih =>
    show (stateTransition (stateOf c) (Block.mk bid _ newSlot votes)).L = _
    simp [stateTransition]

/-- The `s` field of a chain's tip-state equals the tip block's slot. -/
lemma chain_state_s_eq_tip_slot {B : Block n} (chain : Chain n B) :
    (stateOf chain).s = B.slot := by
  induction chain with
  | genesis => simp [stateOf, State.genesis, Block.slot]
  | @extend parent c bid newSlot votes hSlot ih =>
    -- Goal: (stateOf (extend ...)).s = (Block.mk bid parent newSlot votes).slot
    -- Unfold stateOf to stateTransition, then unfold to processBlock + iterate.
    show (stateTransition (stateOf c) (Block.mk bid parent newSlot votes)).s
        = (Block.mk bid parent newSlot votes).slot
    unfold stateTransition
    rw [processHeight_s, processBlock_s, iterateProcessSlot_s_eq, ih]
    -- Goal: parent.slot + ((Block.mk ...).slot - parent.slot)
    --     = (Block.mk ...).slot. Reduce the slot projection and use hSlot.
    have : (Block.mk bid parent newSlot votes).slot = newSlot := rfl
    rw [this]
    omega

/-! ### One-step h bound and successor view of iterateProcessSlot.

`(processSlot σ).h ≤ σ.h + 1` — height advances by at most 1 per slot.
And `iterateProcessSlot σ (k+1) = processSlot (iterateProcessSlot σ k)` —
the "step at the end" view, dual to the definition's "step at the start". -/

/-- `processHeight` advances `h` by at most 1. -/
lemma processHeight_h_le_succ (σ : State n) :
    (processHeight σ).h ≤ σ.h + 1 := by
  rcases (height_progression σ).1 with h | h
  · rw [h]; omega
  · rw [h]

/-- `processSlot` advances `h` by at most 1. -/
lemma processSlot_h_le_succ (σ : State n) :
    (processSlot σ).h ≤ σ.h + 1 := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_h_le_succ σ
  · simp [processSlot, hEmpty]

/-- `iterateProcessSlot σ (k+1) = processSlot (iterateProcessSlot σ k)`.
    The "step at the end" view of the iteration. -/
lemma iterateProcessSlot_succ_apply (σ : State n) (k : ℕ) :
    iterateProcessSlot σ (k + 1) = processSlot (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => rfl
  | succ k ih =>
    show iterateProcessSlot (processSlot σ) (k + 1) = processSlot (iterateProcessSlot σ (k + 1))
    rw [ih (processSlot σ)]
    -- Goal: processSlot (iterateProcessSlot (processSlot σ) k) = processSlot (iterateProcessSlot σ (k+1))
    -- Both sides are processSlot of iterateProcessSlot (processSlot σ) k, but the RHS unfolds to that.
    rfl

/-- Companion: `(iterateProcessSlot σ (k+1)).h ≤ (iterateProcessSlot σ k).h + 1`. -/
lemma iterateProcessSlot_h_step_bound (σ : State n) (k : ℕ) :
    (iterateProcessSlot σ (k + 1)).h ≤ (iterateProcessSlot σ k).h + 1 := by
  rw [iterateProcessSlot_succ_apply]
  exact processSlot_h_le_succ _

/-! ### First-crossing lemma for `iterateProcessSlot`

If `iterateProcessSlot σ k`'s height has surpassed `h_f`, but `σ.h ≤ h_f`,
then there is a unique `k₀ < k` such that `(iterateProcessSlot σ k₀).h = h_f`
AND the next iteration is the one that advances h to h_f+1. The pre-state
at that crossing has the height-advance quorum (justification or timeout)
on its targets/timeouts arrays. -/

/-- If `iterateProcessSlot σ k` has surpassed height `h_f` while `σ.h ≤ h_f`,
    there is a unique `k₀ < k` such that the (k₀ + 1)-th iteration is the
    one that crosses h from `h_f` to `h_f + 1`. The pre-state at that
    crossing has the height-advance quorum on its targets/timeouts arrays. -/
lemma iterateProcessSlot_first_crossing (σ : State n) (h_f k : ℕ)
    (h_lo : σ.h ≤ h_f) (h_hi : (iterateProcessSlot σ k).h > h_f) :
    ∃ k₀, k₀ < k ∧ (iterateProcessSlot σ k₀).h = h_f ∧
      (iterateProcessSlot σ (k₀ + 1)).h = h_f + 1 := by
  -- Take the SMALLEST j with (iterateProcessSlot σ j).h > h_f.
  have h_pred : ∃ j, (iterateProcessSlot σ j).h > h_f := ⟨k, h_hi⟩
  have hj_spec : (iterateProcessSlot σ (Nat.find h_pred)).h > h_f := Nat.find_spec h_pred
  have hj_min : ∀ m < Nat.find h_pred,
      ¬ (iterateProcessSlot σ m).h > h_f := fun m hm => Nat.find_min h_pred hm
  -- j > 0: else j = 0 means σ.h > h_f, contradicting h_lo.
  have hj_pos : Nat.find h_pred > 0 := by
    by_contra h_le
    have h_le' : Nat.find h_pred = 0 := by omega
    rw [h_le'] at hj_spec
    simp [iterateProcessSlot] at hj_spec
    omega
  -- Set k₀ := j - 1.
  set j := Nat.find h_pred
  refine ⟨j - 1, ?_, ?_, ?_⟩
  · -- j - 1 < k. We have j ≤ k from Nat.find_le with witness k.
    have hj_le_k : j ≤ k := Nat.find_le h_hi
    omega
  · -- (iterateProcessSlot σ (j - 1)).h = h_f.
    have h_jm1_le : (iterateProcessSlot σ (j - 1)).h ≤ h_f := by
      have := hj_min (j - 1) (Nat.sub_lt hj_pos one_pos)
      omega
    have h_eq : j = (j - 1) + 1 := (Nat.succ_pred_eq_of_pos hj_pos).symm
    have h_step_bound :
        (iterateProcessSlot σ j).h ≤ (iterateProcessSlot σ (j - 1)).h + 1 := by
      rw [h_eq]
      exact iterateProcessSlot_h_step_bound σ (j - 1)
    omega
  · -- (iterateProcessSlot σ ((j - 1) + 1)).h = h_f + 1.
    have h_eq : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos hj_pos
    rw [h_eq]
    have h_jm1_le : (iterateProcessSlot σ (j - 1)).h ≤ h_f := by
      have := hj_min (j - 1) (Nat.sub_lt hj_pos one_pos)
      omega
    have h_step_bound :
        (iterateProcessSlot σ j).h ≤ (iterateProcessSlot σ (j - 1)).h + 1 := by
      rw [show j = (j - 1) + 1 from (Nat.succ_pred_eq_of_pos hj_pos).symm]
      exact iterateProcessSlot_h_step_bound σ (j - 1)
    omega

/-! ### Chain uniqueness

The type `Chain n B` is essentially a singleton: every chain ending at `B`
is structurally the same, except for slot-inequality proof terms, which are
proof-irrelevant. The state `stateOf` therefore depends only on the tip
block. -/

/-- Chain uniqueness: any two chains ending at the same block produce the
    same state. -/
lemma chain_unique {B : Block n} (chain1 chain2 : Chain n B) :
    stateOf chain1 = stateOf chain2 := by
  induction chain1 with
  | genesis =>
    -- chain2 must also be genesis (both at Block.genesis).
    cases chain2
    rfl
  | @extend parent c1 bid newSlot votes hSlot1 ih =>
    -- chain2 must also be an extend with the same tip.
    cases chain2 with
    | extend c2 _ _ _ hSlot2 =>
      -- stateOf chain1 = stateTransition (stateOf c1) (mk bid parent newSlot votes)
      -- stateOf chain2 = stateTransition (stateOf c2) (mk bid parent newSlot votes)
      -- By IH, stateOf c1 = stateOf c2.
      show stateTransition (stateOf c1) _ = stateTransition (stateOf c2) _
      rw [ih c2]

/-! ### Subchain extraction

(Subchain extraction is defined earlier, before `IsFinalizedAt`.) -/

private theorem ancestor_genesis_eq {B' : Block n}
    (h : B' ≼ Block.genesis) : B' = Block.genesis := by
  cases h with
  | refl => rfl

private theorem ancestor_mk_cases {B' parent : Block n} {bid s : ℕ} {vs : List (Vote n)}
    (h : B' ≼ Block.mk bid parent s vs) :
    B' = Block.mk bid parent s vs ∨ B' ≼ parent := by
  cases h with
  | refl => exact Or.inl rfl
  | step h' => exact Or.inr h'

/-! ### State-height monotonicity along ≼

For any chain and any ancestor `B' ≼ B`, the state-height of the subchain
at `B'` is at most the state-height at the tip. This is Lemma 2's
state-height monotonicity. -/

/-- The subchain at the tip via `refl` produces a chain whose state matches
    the original (up to the `hEq ▸ ...` rewrite). -/
@[simp] lemma Chain.subchain_refl_eq {B : Block n} (chain : Chain n B) :
    chain.subchain (Block.Ancestor.refl B) = chain := by
  cases chain with
  | genesis =>
    -- subchain (.genesis) (.refl genesis) = (rfl ▸ .genesis) = .genesis.
    rfl
  | extend c bid newSlot votes hSlot =>
    -- subchain (.extend c _ _) (.refl _) takes the `if` true branch.
    show (if hEq : (Block.mk bid _ newSlot votes) = Block.mk bid _ newSlot votes then
            hEq ▸ Chain.extend c bid newSlot votes hSlot
          else _) = _
    simp

/-- State-height is non-decreasing along the prefix-of-chain order. -/
lemma stateOf_subchain_h_le {B : Block n} (chain : Chain n B) :
    ∀ {B' : Block n} (h_anc : B' ≼ B),
    (stateOf (chain.subchain h_anc)).h ≤ (stateOf chain).h := by
  induction chain with
  | genesis =>
    intro B' h_anc
    have hB' : B' = Block.genesis := ancestor_genesis_eq h_anc
    subst hB'
    -- Now subchain (.genesis) h_anc = .genesis (regardless of h_anc structure).
    show (stateOf ((Chain.genesis : Chain n _).subchain h_anc)).h ≤
          (stateOf (Chain.genesis : Chain n _)).h
    -- Force h_anc to refl form via cases:
    cases h_anc
    exact le_refl _
  | @extend parent c bid newSlot votes hSlot ih =>
    intro B' h_anc
    -- Decision: is B' = Block.mk bid parent newSlot votes?
    by_cases hEq : B' = Block.mk bid parent newSlot votes
    · -- Yes: subchain returns the chain itself (the `if` true branch).
      subst hEq
      -- Goal: (stateOf (subchain (extend c _ _) h_anc)).h ≤ ...
      show (stateOf ((Chain.extend c bid newSlot votes hSlot).subchain h_anc)).h ≤
            (stateOf (Chain.extend c bid newSlot votes hSlot)).h
      -- The if reduces to the true branch:
      have h_eq_refl : (Chain.extend c bid newSlot votes hSlot).subchain h_anc =
                       Chain.extend c bid newSlot votes hSlot := by
        show (if hEq2 : Block.mk bid parent newSlot votes = Block.mk bid parent newSlot votes then
                hEq2 ▸ Chain.extend c bid newSlot votes hSlot
              else _) = _
        simp
      rw [h_eq_refl]
    · -- No: subchain recurses on c.
      have h_step : B' ≼ parent := by
        rcases ancestor_mk_cases h_anc with hR | hS
        · exact absurd hR hEq
        · exact hS
      -- subchain reduces to subchain c h_step:
      have h_eq_rec : (Chain.extend c bid newSlot votes hSlot).subchain h_anc =
                      c.subchain h_step := by
        show (if hEq2 : B' = Block.mk bid parent newSlot votes then
                hEq2 ▸ Chain.extend c bid newSlot votes hSlot
              else c.subchain _) = _
        rw [dif_neg hEq]
      rw [h_eq_rec]
      -- Goal: (stateOf (c.subchain h_step)).h ≤ (stateOf (extend c _ _)).h
      have h1 : (stateOf (c.subchain h_step)).h ≤ (stateOf c).h := ih h_step
      have h2 : (stateOf c).h ≤ (stateOf (Chain.extend c bid newSlot votes hSlot)).h := by
        show (stateOf c).h ≤
            (stateTransition (stateOf c) (Block.mk bid parent newSlot votes)).h
        exact stateTransition_h_le _ _
      exact h1.trans h2

/-! ### Slot-iteration height monotonicity -/

lemma iterateProcessSlot_h_le (σ : State n) (k : ℕ) :
    σ.h ≤ (iterateProcessSlot σ k).h := by
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]
  | succ k ih =>
    show σ.h ≤ (iterateProcessSlot (processSlot σ) k).h
    exact (processSlot_h_le σ).trans (ih (processSlot σ))

end AccountableSafety
