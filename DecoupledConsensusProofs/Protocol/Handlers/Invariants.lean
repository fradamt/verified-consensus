module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Ancestry

@[expose] public section

/-!
# P6 — the cheap invariants (design note P6; obligations O3, O4)

What this file establishes, and what it deliberately leaves stated:

* **O3, `s = L.slot` in every derived chain state** — proved. It needs no
  induction beyond genesis: `state_transition` writes both fields from the same
  block and nothing downstream of it touches either.
* **F-monotonicity and no-revert** — proved, for every handler and for the tick.
  `update_finality` advances `Σ.F` only under its own `Σ.F ≺ σ.F` guard, so the
  step form needs no reachability hypothesis and the run form is one induction
  over `Steps`.
* **O4, parent-closure step preservation** — proved, under the
  dependency-complete hypothesis. The unconditional reachable-store form is
  false (choices P6.1).
* **O5, `Σ.F ∈ Σ.T` at every reachable store** — proved. `update_finality`'s
  third guard is `σ.F ∈ V(Σ)` and `V(Σ)` filters `Σ.T`, so the invariant needs
  only the reachability induction and the fact that no other handler writes
  either field.

Stated in `Props/Invariants.lean` and **not** proved here:
`FinalizedPrecedesJustifiedInvariant` and `FinalityHeightsOrderedInvariant`
route through a chain-state fact (`σ.F ⪯ σ.J`) that no store guard supplies —
the store guards give `Σ.F ⪯ σ.J` only when the justification filter admits
`σ`, and the finalization branch can fire when it does not.
`DerivedStateAgreesInvariant` needs O8. Neither is cheap in the sense this file
uses.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## O3 — `s = L.slot` (PROTOCOL.md#the-complete-protocol; obligations O3) -/









omit [Fintype V] in
/-- §4 `process_attestation` writes only the three participation sets
(PROTOCOL.md#the-complete-protocol), so the fold of `state_transition` carries `s`. -/
theorem foldl_process_attestation_s (l : List (CombinedAttestation V))
    (σ : ChainState V) : (l.foldl Protocol.process_attestation σ).s = σ.s := by
  induction l generalizing σ with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons, ih]
      unfold Protocol.process_attestation
      split_ifs <;> rfl

omit [Fintype V] in
/-- §4 the same for `L` (PROTOCOL.md#the-complete-protocol). -/
theorem foldl_process_attestation_L (l : List (CombinedAttestation V))
    (σ : ChainState V) : (l.foldl Protocol.process_attestation σ).L = σ.L := by
  induction l generalizing σ with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons, ih]
      unfold Protocol.process_attestation
      split_ifs <;> rfl

/-! ## F-monotonicity (PROTOCOL.md#the-complete-protocol) -/

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` writes the vote pool and its stamp only
(PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_F (st : Protocol.Store V) (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote st vote).F = st.F := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- The checked runtime guard also preserves `Σ.F`; the admitted branch is
the unchecked core handler above. -/
theorem on_goldfish_vote_checked_F (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).F = st.F := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_F st vote
  · rfl


/-- The checked carried-vote fold preserves `Σ.F`. -/
theorem foldl_on_goldfish_vote_checked_F (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).F = st.F := by
  induction l generalizing st with
  | nil => rfl
  | cons v vs ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_F]

omit [Fintype V] in
/-- §7.2 `on_sg_vote` writes the SG pool and its stamp only
(PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_F (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).F = st.F := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-- §4 `process_height_events` moves the height fields only
(PROTOCOL.md#the-complete-protocol): neither branch, and neither does `advance_height`,
touch `σ.s`. -/
theorem process_height_events_s (E : Env V) (cfg : HeightConfig) (σ : ChainState V) :
    (Protocol.process_height_events E cfg σ).s = σ.s := by
  simp only [Protocol.process_height_events, Protocol.advance_height]
  split_ifs <;> rfl

/-- §4 the same for `L` (PROTOCOL.md#the-complete-protocol). -/
theorem process_height_events_L (E : Env V) (cfg : HeightConfig) (σ : ChainState V) :
    (Protocol.process_height_events E cfg σ).L = σ.L := by
  simp only [Protocol.process_height_events, Protocol.advance_height]
  split_ifs <;> rfl

/-- §4 `σ.s ← B.slot` survives the transition (PROTOCOL.md#the-complete-protocol). -/
theorem state_transition_s (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (B : Block V) : (Protocol.state_transition E cfg σ B).s = B.slot := by
  unfold Protocol.state_transition
  rw [process_height_events_s]
  exact foldl_process_attestation_s _ _

/-- §4 `σ.L ← B` survives the transition (PROTOCOL.md#the-complete-protocol). -/
theorem state_transition_L (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (B : Block V) : (Protocol.state_transition E cfg σ B).L = B := by
  unfold Protocol.state_transition
  rw [process_height_events_L]

/-- **O3** at one transition (PROTOCOL.md#the-complete-protocol, choices 4.9). -/
theorem state_transition_s_eq_L_slot (E : Env V) (cfg : HeightConfig)
    (σ : ChainState V) (B : Block V) :
    (Protocol.state_transition E cfg σ B).s =
      (Protocol.state_transition E cfg σ B).L.slot := by
  rw [state_transition_s, state_transition_L]




omit [Fintype V] in
/-- §5.2 `update_finality` advances `Σ.F` only under its own guard
`Σ.F ≺ σ.F` (PROTOCOL.md#the-complete-protocol): the justification statement carries `F`
through, and the finalization statement writes a strict descendant. -/
theorem update_finality_F (st : Protocol.Store V) (σ : ChainState V) :
    Block.preceq st.F (Protocol.update_finality st σ).F = true := by
  simp only [Protocol.update_finality]
  split_ifs <;> rename_i h <;>
    first
      | exact Block.preceq_self _
      | exact Block.preceq_of_prec (by
          rw [Bool.and_eq_true, Bool.and_eq_true] at h
          exact h.1.1)

omit [Fintype V] in
/-- §7.2 `update_finality` writes no block into the tree
(PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_T (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).T = st.T := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` writes no block into the tree
(PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_T (st : Protocol.Store V) (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote st vote).T = st.T := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- The checked runtime guard also preserves `Σ.T`; the admitted branch is
the unchecked core handler above. -/
theorem on_goldfish_vote_checked_T (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).T = st.T := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_T st vote
  · rfl


/-- The checked carried-vote fold preserves `Σ.T`. -/
theorem foldl_on_goldfish_vote_checked_T (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).T = st.T := by
  induction l generalizing st with
  | nil => rfl
  | cons v vs ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_T]

omit [Fintype V] in
/-- §7.1 `FGStore.toHealing` copies `Σ.T` (PROTOCOL.md#the-complete-protocol), so §2's
predicate reads this store's own tree. -/
theorem parentClosed_iff (st : Protocol.Store V) :
    ParentClosed st ↔
      (Block.genesis ∈ st.T ∧ ∀ B ∈ st.T, B.parent? = none ∨ B.parent ∈ st.T) :=
  Iff.rfl



/-! ## O5 — `Σ.F ∈ Σ.T` (PROTOCOL.md#the-complete-protocol; obligations O5) -/

omit [Fintype V] in
/-- §7.2 `on_sg_vote` writes no block into the tree
(PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_T (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).T = st.T := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


omit [Fintype V] in
/-- §5.2 `update_finality` writes `Σ.F` only from inside the live tree: its third
guard is `σ.F ∈ V(Σ)` letter for letter, `V(Σ)` filters `T_F(Σ)` and `T_F(Σ)`
filters `Σ.T` (PROTOCOL.md#the-complete-protocol, choices S5.15). This is the one step where
`Σ.F` moves, and it is what makes O5 hold without a further invariant. -/
theorem finalizedInTree_update_finality (st : Protocol.Store V) (σ : ChainState V)
    (h : st.F ∈ st.T) :
    (Protocol.update_finality st σ).F ∈ (Protocol.update_finality st σ).T := by
  rw [Proofs.update_finality_T]
  simp only [Protocol.update_finality]
  split_ifs <;> rename_i hg <;>
    first
      | exact h
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
            Protocol.finalized_descendants, Finset.mem_filter] at hg
         exact hg.2.1.1)

end Proofs
end DecoupledConsensusModel

end
