module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants

@[expose] public section

/-!
# P6 — the store invariant pack (design note P6; obligations O4, O5, O8)

`Invariants.lean` proves the invariants a single handler settles: O3,
F-monotonicity, O4's step form and O5. This file proves the four that need an
induction over `Internal.Reachable`, and the two that need the dependency-complete
contract (O8) on top of it.

Three shapes are forced here.

* **The chain state carries its own finality invariant.** `ChainFinality`
  supplies `σ.h_F ≤ σ.h_j` and `σ.F ⪯ σ.J`, and `StoreChainStates` carries it
  over the whole of `Σ.σ[·]`. It needs no
  dependency hypothesis: `Σ.σ[·]` is written only by `on_block`, always as
  `state_transition(Σ.σ[B.parent], B)`, and the default entry is
  `ChainState.initial`, which satisfies it.
* **`ChainFinality` has to carry ancestry as well as heights.** The height half
  alone is not inductive: `process_height_events`' justification branch writes
  `(J, h_j) ← (T_h, h)` (PROTOCOL.md#the-complete-protocol), so `F ⪯ J` at the next state
  is `F ⪯ T_h` at this one. The chain `F ⪯ J ⪯ T_h ⪯ L` is what closes it, and
  the last link is why `state_transition` preserves the invariant only for a
  block that extends `σ.L` — which is `σ[B] = state_transition(σ[B.parent], B)`
  read as the model applies it (PROTOCOL.md#the-complete-protocol).
* **O4 and the P1 bridge are stated over a dependency-complete run.** The
  unconditional forms are false (choices P6.1): `on_block` inserts `B` with
  no parent test, and re-derives `σ[B]` from whatever `Σ.σ[B.parent]` holds.
  `DepStep` is `Internal.Step` with the contract of PROTOCOL.md#the-complete-protocol attached
  to the one constructor that consumes it — and to `on_tick`, because the tick
  self-processes its own proposal (PROTOCOL.md#the-complete-protocol), which no constraint
  on delivered objects reaches.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record HeightId)
open Protocol (HealConfig)
open Internal

/-! ## Ancestry and the justification order -/

section Ancestry

variable {V : Type} [DecidableEq V]

/-- §1 genesis precedes every block (PROTOCOL.md#the-complete-protocol). The walk of
`Block.preceq` bottoms out at the `genesis` constructor. -/
theorem preceq_genesis (B : Block V) : Block.preceq Block.genesis B = true := by
  induction B with
  | genesis => simp [Block.preceq]
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr ih

/-- §1 `B.parent ⪯ B`, genesis included, since genesis is its own parent
(PROTOCOL.md#the-complete-protocol; `Substrate/Blocks.lean` `Block.parent`). -/
theorem preceq_parent (B : Block V) : Block.preceq B.parent B = true := by
  cases B with
  | genesis => exact Block.preceq_self _
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent, Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self _)

omit [DecidableEq V] in
/-- §1 the total `B.parent` agrees with the partial `B.parent?` wherever the
latter is defined (PROTOCOL.md#the-complete-protocol, F1.1). -/
theorem parent_eq_of_parent? {B P : Block V} (h : B.parent? = some P) :
    B.parent = P := by
  cases B with
  | genesis => simp [Block.parent?] at h
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at h
      simpa only [Block.parent] using h

end Ancestry

/-- §5 the lexicographic justification order compares heights first
(PROTOCOL.md#the-complete-protocol), so it dominates `h_j`. -/
theorem heightId_height_le_of_le {a b : HeightId} (h : a ≤ b) :
    a.height ≤ b.height := by
  have h' : toLex (a.height, a.id) ≤ toLex (b.height, b.id) := h
  exact (Prod.Lex.toLex_le_toLex'.mp h').1


/-! ## The §4 chain-state invariant (PROTOCOL.md#the-complete-protocol) -/

section ChainStateInvariant

variable {V : Type} [DecidableEq V]

/-- §4 the finality invariant of a chain state (PROTOCOL.md#the-complete-protocol,
644–658).

The document states none of this; it is what makes `update_finality`'s store
claim (PROTOCOL.md#the-complete-protocol) true, and it is the weakest bundle closed under
`state_transition`. The ancestry chain `F ⪯ J ⪯ T_h ⪯ L` is needed because
`process_height_events` moves `J ← T_h` and `T_h ← L`, so each link is the next
one's induction hypothesis. -/
structure ChainFinality (σ : ChainState V) : Prop where
  /-- §4 `T_h` is on the chain ending at the latest block
  (PROTOCOL.md#the-complete-protocol). -/
  target_preceq_latest : Block.preceq σ.T_h σ.L = true
  /-- §4 the justification is at or below the height target
  (PROTOCOL.md#the-complete-protocol). -/
  justified_preceq_target : Block.preceq σ.J σ.T_h = true
  /-- §4 `F ⪯ J`, the chain-state half of PROTOCOL.md#the-complete-protocol. -/
  finalized_preceq_justified : Block.preceq σ.F σ.J = true
  /-- §4 `h_F ≤ h_j` (PROTOCOL.md#the-complete-protocol). -/
  heights_ordered : σ.h_F ≤ σ.h_j
  /-- §4 the justification is strictly below the current height: the write
  `(J, h_j) ← (T_h, h)` is followed by `h ← h + 1`
  (PROTOCOL.md#the-complete-protocol, F4.6). -/
  justified_below_height : σ.h_j < σ.h

/-- §4 the initial chain state satisfies it: every block field is genesis and
`h_j = 0 < 1 = h` (PROTOCOL.md#the-complete-protocol). -/
theorem chainFinality_initial : ChainFinality (ChainState.initial : ChainState V) :=
  { target_preceq_latest := Block.preceq_self _
    justified_preceq_target := Block.preceq_self _
    finalized_preceq_justified := Block.preceq_self _
    heights_ordered := Nat.le_refl 0
    justified_below_height := Nat.zero_lt_one }

/-- §4 `process_attestation` writes the three participation sets and nothing
else (PROTOCOL.md#the-complete-protocol), so every field `ChainFinality` reads is carried. -/
theorem process_attestation_fields (σ : ChainState V) (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).L = σ.L ∧
      (Protocol.process_attestation σ a).h = σ.h ∧
      (Protocol.process_attestation σ a).T_h = σ.T_h ∧
      (Protocol.process_attestation σ a).J = σ.J ∧
      (Protocol.process_attestation σ a).h_j = σ.h_j ∧
      (Protocol.process_attestation σ a).F = σ.F ∧
      (Protocol.process_attestation σ a).h_F = σ.h_F := by
  unfold Protocol.process_attestation
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- §4 the same across the attestation fold of `state_transition`
(PROTOCOL.md#the-complete-protocol). -/
theorem foldl_process_attestation_fields (l : List (CombinedAttestation V))
    (σ : ChainState V) :
    (l.foldl Protocol.process_attestation σ).L = σ.L ∧
      (l.foldl Protocol.process_attestation σ).h = σ.h ∧
      (l.foldl Protocol.process_attestation σ).T_h = σ.T_h ∧
      (l.foldl Protocol.process_attestation σ).J = σ.J ∧
      (l.foldl Protocol.process_attestation σ).h_j = σ.h_j ∧
      (l.foldl Protocol.process_attestation σ).F = σ.F ∧
      (l.foldl Protocol.process_attestation σ).h_F = σ.h_F := by
  induction l generalizing σ with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (Protocol.process_attestation σ a)
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := process_attestation_fields σ a
      rw [List.foldl_cons]
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4, h5.trans g5,
        h6.trans g6, h7.trans g7⟩



variable [Fintype V]

/-- §4 `process_height_events` preserves the invariant (PROTOCOL.md#the-complete-protocol).

The finality branch writes `F ← J`, which is the reflexive case of `F ⪯ J`; the
justification branch writes `J ← T_h` and `h_j ← h`, which is where
`J ⪯ T_h` and `h_j < h` are spent; `advance_height` writes `T_h ← L` and
`h ← h + 1`, which is where `T_h ⪯ L` is spent. No guard is read. -/
theorem chainFinality_process_height_events (E : Env V) (cfg : HeightConfig)
    (σ : ChainState V) (h : ChainFinality σ) :
    ChainFinality (Protocol.process_height_events E cfg σ) := by
  simp only [Protocol.process_height_events, Protocol.advance_height]
  split_ifs
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target := h.target_preceq_latest
        finalized_preceq_justified := h.justified_preceq_target
        heights_ordered := Nat.le_of_lt h.justified_below_height
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target :=
          Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
        finalized_preceq_justified := Block.preceq_self _
        heights_ordered := Nat.le_refl _
        justified_below_height := Nat.lt_succ_of_lt h.justified_below_height }
  · exact
      { target_preceq_latest := h.target_preceq_latest
        justified_preceq_target := h.justified_preceq_target
        finalized_preceq_justified := Block.preceq_self _
        heights_ordered := Nat.le_refl _
        justified_below_height := h.justified_below_height }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target := h.target_preceq_latest
        finalized_preceq_justified :=
          Block.preceq_trans h.finalized_preceq_justified h.justified_preceq_target
        heights_ordered :=
          Nat.le_of_lt (Nat.lt_of_le_of_lt h.heights_ordered h.justified_below_height)
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target :=
          Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
        finalized_preceq_justified := h.finalized_preceq_justified
        heights_ordered := h.heights_ordered
        justified_below_height := Nat.lt_succ_of_lt h.justified_below_height }
  · exact h


/-- §4 `state_transition` preserves the invariant for a block that extends the
state's latest block (PROTOCOL.md#the-complete-protocol).

The hypothesis `σ.L ⪯ B` is the parent-extension condition used by the state
map induction. -/
theorem chainFinality_state_transition (E : Env V) (cfg : HeightConfig)
    (σ : ChainState V) (B : Block V) (h : ChainFinality σ)
    (hL : Block.preceq σ.L B = true) :
    ChainFinality (Protocol.state_transition E cfg σ B) := by
  unfold Protocol.state_transition
  refine chainFinality_process_height_events E cfg _ ?_
  obtain ⟨_, f2, f3, f4, f5, f6, f7⟩ :=
    foldl_process_attestation_fields B.attestations ({ σ with s := B.slot } : ChainState V)
  exact
    { target_preceq_latest := by
        rw [f3]; exact Block.preceq_trans h.target_preceq_latest hL
      justified_preceq_target := by
        rw [f3, f4]; exact h.justified_preceq_target
      finalized_preceq_justified := by
        rw [f4, f6]; exact h.finalized_preceq_justified
      heights_ordered := by
        rw [f5, f7]; exact h.heights_ordered
      justified_below_height := by
        rw [f2, f5]; exact h.justified_below_height }

end ChainStateInvariant

/-! ## The store's state map and its finality core -/

section StoreInvariant

variable {V : Type} [DecidableEq V] [Fintype V]

/-- P6 the invariant of a store's state map `Σ.σ[·]` (PROTOCOL.md#the-complete-protocol,
731–732): every entry is the post-state of a chain ending at its own key, and
every entry satisfies the §4 invariant.

The first conjunct is what makes the second inductive — it is the hypothesis
`chainFinality_state_transition` needs at `B.parent`. -/
def ChainStatesOk (m : Block V → ChainState V) : Prop :=
  ∀ C : Block V, Block.preceq (m C).L C = true ∧ ChainFinality (m C)

/-- P6 the same, read off a store. -/
def StoreChainStates (st : Protocol.Store V) : Prop :=
  ChainStatesOk st.σ

omit [Fintype V] in
/-- P6 the default map of `FGStore.init` is the constant initial chain state
(PROTOCOL.md#the-complete-protocol, modeling-choices row 3); its `L` is genesis, which
precedes every key. -/
theorem chainStatesOk_const_initial :
    ChainStatesOk (fun _ : Block V => (ChainState.initial : ChainState V)) :=
  fun C => ⟨preceq_genesis C, chainFinality_initial⟩

/-- P6 `on_block`'s write to `Σ.σ[·]` preserves the map invariant. -/
theorem chainStatesOk_write (E : Env V) (cfg : HeightConfig)
    (m : Block V → ChainState V) (B : Block V) (h : ChainStatesOk m) :
    ChainStatesOk (fun C => if C = B then
      Protocol.state_transition E cfg (m B.parent) B else m C) := by
  intro C
  by_cases hC : C = B
  · refine ⟨?_, ?_⟩ <;> simp only [if_pos hC]
    · rw [hC, state_transition_L]
      exact Block.preceq_self _
    · exact chainFinality_state_transition E cfg _ B (h B.parent).2
        (Block.preceq_trans (h B.parent).1 (preceq_parent B))
  · refine ⟨?_, ?_⟩ <;> simp only [if_neg hC]
    · exact (h C).1
    · exact (h C).2


/-- P6 the four fields the invariant pack reads: the state map and the three
stored finality fields (PROTOCOL.md#the-complete-protocol). A handler that leaves all four alone
preserves every statement below, which is three of the four handlers and four of
the five tick branches. -/
structure CoreEq (st st' : Protocol.Store V) : Prop where
  /-- `Σ.σ[·]` is carried. -/
  σ_eq : st'.σ = st.σ
  /-- `Σ.F` is carried. -/
  F_eq : st'.F = st.F
  /-- `Σ.J` is carried. -/
  J_eq : st'.J = st.J
  /-- `Σ.h_j` is carried. -/
  h_j_eq : st'.h_j = st.h_j

namespace CoreEq

omit [DecidableEq V] [Fintype V] in
/-- Reflexivity. -/
theorem refl' (st : Protocol.Store V) : CoreEq st st :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- Transitivity. -/
theorem trans' {a b c : Protocol.Store V} (h₁ : CoreEq a b) (h₂ : CoreEq b c) :
    CoreEq a c :=
  ⟨h₂.σ_eq.trans h₁.σ_eq, h₂.F_eq.trans h₁.F_eq,
    h₂.J_eq.trans h₁.J_eq, h₂.h_j_eq.trans h₁.h_j_eq⟩

omit [Fintype V] in
/-- A core-preserving handler also preserves the derived finalized-height
view. This is a consequence of carrying `F` and `σ`, not a stored field. -/
theorem finalized_height_eq {st st' : Protocol.Store V} (h : CoreEq st st') :
    st'.finalized_height = st.finalized_height := by
  simp only [Protocol.Store.finalized_height, h.F_eq, h.σ_eq]

end CoreEq

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` writes the vote pool and its stamp only
(PROTOCOL.md#the-complete-protocol). -/
theorem coreEq_on_goldfish_vote (st : Protocol.Store V) (vote : GoldfishVote V) :
    CoreEq st (Protocol.on_goldfish_vote st vote) := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The checked runtime guard preserves the same core fields; its admitted
branch is the unchecked core handler above. -/
theorem coreEq_on_goldfish_vote_checked (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    CoreEq st (Protocol.on_goldfish_vote_checked E st vote) := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact coreEq_on_goldfish_vote st vote
  · exact CoreEq.refl' st


/-- The checked carried-vote fold preserves the core fields. -/
theorem coreEq_foldl_on_goldfish_vote_checked (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    CoreEq st (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l generalizing st with
  | nil => exact CoreEq.refl' _
  | cons v vs ih =>
      rw [List.foldl_cons]
      exact CoreEq.trans' (coreEq_on_goldfish_vote_checked E st v) (ih _)

omit [Fintype V] in
/-- §7.2 `on_sg_vote` writes the SG pool and its stamp only
(PROTOCOL.md#the-complete-protocol). -/
theorem coreEq_on_sg_vote (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : CoreEq st (Protocol.on_sg_vote hc st a) := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### The core fields, one projection at a time

`Invariants.lean` already has the `F` and `T` families; these are the three the
tick proofs below rewrite with, in the same style (`simp only` through the
branch nest, which is cheap where an `exact` against a whole store is not). -/














omit [Fintype V] in
/-- §5.2 `update_finality` writes the finality fields, never the state map
(PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_σ (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).σ = st.σ := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

/-! ### `Σ.F ⪯ Σ.J` at `update_finality` -/

omit [Fintype V] in
/-- §5.2 `update_finality` preserves `Σ.F ⪯ Σ.J` (PROTOCOL.md#the-complete-protocol,
744–750).

This needs no chain-state fact: each of the branches that writes gets the claim
from its **own** guard. The justification statement writes `J ← σ.J` under
`Σ.F ⪯ σ.J`; the finalization statement writes `F ← σ.F` under `σ.F ⪯ Σ.J`,
reading the `Σ.J` the first statement may have just written (F5.2); and the
induction hypothesis is consumed only when neither fires. -/
theorem update_finality_preceq (st : Protocol.Store V) (σ : ChainState V)
    (h : Block.preceq st.F st.J = true) :
    Block.preceq (Protocol.update_finality st σ).F
      (Protocol.update_finality st σ).J = true := by
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h₂
    exact h₂.1.2
  · rw [Bool.and_eq_true] at h₁
    exact h₁.1
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h₃
    exact h₃.1.2
  · exact h

/-! ### The bundle carried by the reachability induction -/

/-- P6 what one induction over `Internal.Reachable` establishes: the state-map
invariant and `Σ.F ⪯ Σ.J` (PROTOCOL.md#the-complete-protocol). -/
def StoreFinality (st : Protocol.Store V) : Prop :=
  StoreChainStates st ∧ FinalizedPrecedesJustified st











omit [Fintype V] in
/-- §5.2 `update_finality` never lowers the justification event: its own guard
is that the new one is lex-greater (PROTOCOL.md#the-complete-protocol), and the
finalization statement does not touch `(Σ.J, Σ.h_j)`. -/
theorem update_finality_heightId (st : Protocol.Store V) (σ : ChainState V) :
    HeightId.mk st.h_j st.J.root ≤
      HeightId.mk (Protocol.update_finality st σ).h_j
        (Protocol.update_finality st σ).J.root := by
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃ <;>
    first
      | exact le_refl _
      | (rw [Bool.and_eq_true, decide_eq_true_eq] at h₁; exact le_of_lt h₁.2)

omit [Fintype V] in
/-- P6 a handler that carries the four core fields carries the bundle. -/
theorem storeFinality_of_coreEq {st st' : Protocol.Store V} (hc : CoreEq st st')
    (h : StoreFinality st) : StoreFinality st' := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · unfold StoreChainStates
    rw [hc.σ_eq]
    exact h₁
  · change Block.preceq st'.F st'.J = true
    rw [hc.F_eq, hc.J_eq]
    exact h₂

omit [Fintype V] in
/-- P6 `update_finality`, called as `on_block` calls it — with `σ = Σ.σ[B]`. -/
theorem storeFinality_update_finality_at (st : Protocol.Store V) (B : Block V)
    (h : StoreFinality st) : StoreFinality (Protocol.update_finality st (st.σ B)) := by
  refine ⟨?_, ?_⟩
  · unfold StoreChainStates
    rw [update_finality_σ]
    exact h.1
  · exact update_finality_preceq st _ h.2

/-- P6 `on_block` preserves the bundle (PROTOCOL.md#the-complete-protocol). -/
theorem storeFinality_on_block (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V) (B : Block V) (h : StoreFinality st) :
    StoreFinality (Protocol.on_block E cfg st B) := by
  unfold Protocol.on_block Protocol.on_block_using
  split_ifs
  · exact h
  · exact h
  · exact h
  · refine storeFinality_update_finality_at _ B ?_
    refine storeFinality_of_coreEq (coreEq_foldl_on_goldfish_vote_checked E _ _) ?_
    have hstored : ChainStatesOk (fun C => if C = B then
        Protocol.state_transition E cfg (st.σ B.parent) B else st.σ C) :=
      chainStatesOk_write E cfg st.σ B h.1
    exact ⟨hstored, h.2⟩
  · exact h

/-- The checked runtime block handler either delegates to the valid-core bundle
preservation theorem or preserves the bundle reflexively. -/
theorem storeFinality_on_block_checked (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Protocol.Store V) (B : Block V) (h : StoreFinality st) :
    StoreFinality (Protocol.on_block_checked E hc cfg st B) := by
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · rw [show Protocol.on_block_checked E hc cfg st B = Protocol.on_block E cfg st B by
      simp [Protocol.on_block_checked, Protocol.on_block_checked_using, hvalid]]
    exact storeFinality_on_block E cfg st B h
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    rw [show Protocol.on_block_checked E hc cfg st B = st by
      simp [Protocol.on_block_checked, Protocol.on_block_checked_using, hfalse]]
    exact h

omit [Fintype V] in
/-- P6 the initial store satisfies the bundle. -/
theorem storeFinality_init :
    StoreFinality (Protocol.Store.init : Protocol.Store V) :=
  ⟨chainStatesOk_const_initial, Block.preceq_self _⟩

end StoreInvariant

/-! ## O4 and the P1 bridge, over a dependency-complete run
(PROTOCOL.md#the-complete-protocol; obligations O4, O8) -/


/-! ### The P1 bridge — `Σ.σ[·]` agrees with the derived state -/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- P1/P6 a handler that carries `Σ.T` and `Σ.σ[·]` carries the agreement
(PROTOCOL.md#the-complete-protocol). -/
theorem derivedStateAgrees_of_eq (E : Env V) (cfg : HeightConfig)
    {st st' : Protocol.Store V} (hT : st'.T = st.T) (hσ : st'.σ = st.σ)
    (h : DerivedStateAgrees E cfg st) : DerivedStateAgrees E cfg st' := by
  intro B hB
  rw [hT] at hB
  rw [hσ]
  exact h B hB

end Proofs
end DecoupledConsensusModel

end
