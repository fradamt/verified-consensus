module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Execution.CertificateUniqueness
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Staleness
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.TimeoutBindingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Execution.BridgesTail

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## 2. Premise (ii), as a theorem

The retired `opening_block_unique`, with the slot freed. Nothing in the proof
ever used that the slot opened a round. -/


/-- ** premise (ii): exactly one admissible slot-`s` block**
(PROTOCOL.md#the-complete-protocol; round E angle 1).

With an honest slot-`s` proposer, no two distinct slot-`s` blocks are ever
processed by honest nodes — at one node or at two, before any cutoff or after
it. So the spoofed-block counterexample that defeats `GradeFormsAt` as literally
stated cannot occur in an admissible run.

Genesis is excluded by the claim hypotheses alone: `Block.genesis.proposer?` is
`none` (F1.1), so `0 < s` is no longer needed here — it survives in the store
form, where it feeds the `ProposerOk` dichotomy.

The whole content is `Unforgeable.unforgeable` at `Object.author`, now a field
read; the two claim hypotheses are what the admission guard supplies at any
store (`proposerOk_stateBefore`), and a mere delivery does not — a rejected
block can claim anything. `DeliveryWellFormed` does **not** help here —
`Object.wellFormed` checks the carried votes and not the proposer. -/
theorem unique_slot_block_core (S : Setup V) {ρ : Run V} (hadm : AdmissibleCore S ρ)
    {s : Slot} (hprop : S.E.proposer s ∈ ρ.honest)
    {v w : V} {B B' : NamedBlock V} {t t' : Time}
    (hB : Run.processes S ρ v (Object.block B) t)
    (hB' : Run.processes S ρ w (Object.block B') t')
    (hBp : B.proposer? = some (S.E.proposer s))
    (hB'p : B'.proposer? = some (S.E.proposer s))
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' := by
  have h₁ := hadm.unforgeable v _ t hB _ hprop
    (show (Object.block B).author = some (S.E.proposer s) from hBp)
  have h₂ := hadm.unforgeable w _ t' hB' _ hprop
    (show (Object.block B').author = some (S.E.proposer s) from hB'p)
  obtain ⟨t₁, -, he₁⟩ := h₁
  obtain ⟨t₂, -, he₂⟩ := h₂
  exact emits_block_unique S hadm.toNamedScheduleWellFormed he₁ he₂ (by rw [hBs, hB's])

theorem unique_slot_block (S : Setup V) {ρ : Run V} (hadm : Admissible S ρ)
    {s : Slot} (hprop : S.E.proposer s ∈ ρ.honest)
    {v w : V} {B B' : NamedBlock V} {t t' : Time}
    (hB : Run.processes S ρ v (Object.block B) t)
    (hB' : Run.processes S ρ w (Object.block B') t')
    (hBp : B.proposer? = some (S.E.proposer s))
    (hB'p : B'.proposer? = some (S.E.proposer s))
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' :=
  unique_slot_block_core S hadm.toNamedAdmissibleCore hprop hB hB' hBp hB'p hBs hB's



/-- Every non-genesis block an honest store holds passed the proposer-assert
admission guard (baseline `7b2efec`). -/
def ProposerOk (E : Env V) (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, B = Block.genesis ∨ B.proposer? = some (E.proposer B.slot)

/-- `ProposerOk` reads only the tree, so any handler that leaves `Σ.T` alone
preserves it. -/
theorem proposerOk_of_T_eq {E : Env V} {st st' : Protocol.Store V}
    (hT : st'.T = st.T) (h : ProposerOk E st) : ProposerOk E st' := by
  intro B hB
  exact h B (by rwa [hT] at hB)

/-! ### The admission guard, restated over the named runtime
`ProposerOk` above is the compatibility-store invariant, still preserved by the raw
`Protocol.on_block_using` handler regardless of which chain-state builder it is
given (`proposerOk_on_block_using` below is `proposerOk_on_block`'s proof,
generalized off `state_transition` — none of its steps read the builder). The
named pipeline (`Protocol.NamedStore.process_block_core`, `on_block_with`,
`admit_row`/`admit_rows`/`admit_carried`, and the tick's own duty chain,
`Protocol.NamedTick.tick`) is layered on that same raw handler plus SG-pool
admission that never touches `Σ.T` (`NamedAdmission.admit_row_core` +
`on_sg_vote_T`), so the same invariant carries through it. This mirrors the
established pattern for the other local store invariants over this pipeline
(`Proofs.NamedStoreRoots.RootsInTree`, `NamedJustificationCarrier.CoreJustifier`,
`Proofs.NamedConfirmationMembership.Confirmed`). -/

private theorem proposerOk_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (h : ProposerOk E st) : ProposerOk E (Protocol.on_block_using E st B buildState) := by
  simp only [Protocol.on_block_using]
  split_ifs with h1 h2 h3
  · exact h
  · exact h
  · exact h
  · intro C hC
    rw [Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T E] at hC
    rcases Finset.mem_insert.mp hC with rfl | hmem
    · exact Or.inr (not_not.mp h3)
    · exact h C hmem
  · exact h

private theorem proposerOk_process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  by_cases hp : B.parent ∈ st.bodies
  · rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp), NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · exact proposerOk_on_block_using E st.core B.erase _ h
    · exact h
  · simpa only [Protocol.NamedStore.process_block_core, if_pos hp] using h

private theorem proposerOk_admit_row (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (a : NamedAttestation V) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  exact proposerOk_of_T_eq (on_sg_vote_T hc st.core a.erase) h

private theorem proposerOk_admit_rows (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V))
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (proposerOk_admit_row E hc st a h)

private theorem proposerOk_admit_carried (E : Env V) (hc : Protocol.HealConfig)
    (admission : Protocol.CarriedAdmission) (before after : Protocol.NamedStore V)
    (B : NamedBlock V) (h : ProposerOk E after.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_carried admission hc before after B).core := by
  cases admission with
  | alsoCarried =>
    dsimp only [Protocol.NamedAdmission.admit_carried]
    split_ifs
    · exact proposerOk_admit_rows E hc after B.attestations h
    · exact h

private theorem proposerOk_on_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).core :=
  proposerOk_admit_carried E hc .alsoCarried st _ B (proposerOk_process_block_core E hc cfg st B h)

private theorem proposerOk_propose_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact proposerOk_on_block_with E hc cfg st _ h

private theorem proposerOk_attest_with (E : Env V) (hc : Protocol.HealConfig)
    (gc : Protocol.GradeContract V) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core :=
  proposerOk_admit_row E hc st _ h

/-- The tick's whole duty chain preserves `ProposerOk`, staged through the
computed-duties closed form (`NamedTick.tick_computed_duties`) exactly as
`NamedNode.confirmation_named_tick` stages `NamedConfirmationMembership`'s
invariant: clock, then proposal, then GF vote, then confirmation update, then
attestation. Only the proposal and attestation steps can touch `Σ.T`
(via `on_block_with`/`admit_row`); GF vote and confirmation update carry their
own `Σ.T`-preservation facts (`Protocol.goldfish_vote_with_T`, and
`update_confirmation_with`'s definition, which never writes `Σ.T`). -/
private theorem proposerOk_named_tick (S : Setup V) (gc : Protocol.GradeContract V) (v : V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : ProposerOk S.E st.core) :
    ProposerOk S.E (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = (S.node v).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : ProposerOk S.E st0.core := h
  have h1 : ProposerOk S.E st1.core := by
    dsimp only [st1]
    split_ifs
    · exact proposerOk_propose_block_with S.E S.hc S.cfg gc (S.node v) st0 h0
    · exact h0
  have h2 : ProposerOk S.E st2.core := by
    dsimp only [st2]
    split_ifs
    · exact proposerOk_of_T_eq
        (Protocol.goldfish_vote_with_T gc S.E S.hc (S.node v) st1.core) h1
    · exact h1
  have h3 : ProposerOk S.E st3.core := by
    dsimp only [st3]
    split_ifs
    · exact proposerOk_of_T_eq rfl h2
    · exact h2
  have hstage : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node v).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st3 record).1
      else st3 := by
    rw [NamedTick.tick_computed_duties]
    dsimp only
    rw [apply_ite (fun out : Protocol.NamedStore V × Protocol.NamedRecord ×
      List (NamedObject V) => out.1)]
  rw [hstage]
  split_ifs
  · exact proposerOk_attest_with S.E S.hc gc (S.node v) st3 record h3
  · exact h3

/-- **`ProposerOk` at every honest store of every prefix.** The initial tree is
`{B_gen}`; every later tree write is the named admission pipeline's, whose
proposal guard checks the field (`proposerOk_named_tick`,
`proposerOk_on_block_with`). -/
theorem proposerOk_stateBefore (S : Setup V) (ρ : Run V) (v : V) :
    ∀ n : Nat, ProposerOk S.E (ρ.stateBefore S n v).st.core := by
  intro n
  induction n with
  | zero =>
      rw [show ρ.stateBefore S 0 v = NamedWorld.init v from
        congrFun (Proofs.NamedRuntime.stateBefore_zero S ρ) v]
      intro B hB
      left
      simpa [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial,
        Protocol.Store.init] using hB
  | succ n ih =>
      rcases hev : ρ.events[n]? with _ | e
      · have hnone : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
          have hs := congrFun (Proofs.NamedRuntime.stateBefore_succ S ρ n) v
          simp only [hev, Option.toList_none, List.foldl_nil] at hs
          exact hs
        rw [hnone]
        exact ih
      · cases e with
        | deliver u o t =>
            by_cases hu : v = u
            · subst hu
              show ProposerOk S.E (NamedRun.stateBefore S ρ (n + 1) v).st.core
              rw [Proofs.NamedRuntime.stateBefore_deliver S ρ hev]
              cases o with
              | block B => exact proposerOk_on_block_with S.E S.hc S.cfg _ B ih
              | gfVote u' =>
                  exact proposerOk_of_T_eq (on_goldfish_vote_checked_T S.E _ u') ih
              | attest a => exact proposerOk_admit_row S.E S.hc _ a ih
            · show ProposerOk S.E (NamedRun.stateBefore S ρ (n + 1) v).st.core
              rw [Proofs.NamedRuntime.stateBefore_other S ρ hev v hu]
              exact ih
        | tick u t =>
            by_cases hu : v = u
            · subst hu
              show ProposerOk S.E (NamedRun.stateBefore S ρ (n + 1) v).st.core
              rw [Proofs.NamedRuntime.stateBefore_tick S ρ hev]
              exact proposerOk_named_tick S _ v (ρ.stateBefore S n v).st
                (ρ.stateBefore S n v).record t ih
            · show ProposerOk S.E (NamedRun.stateBefore S ρ (n + 1) v).st.core
              rw [Proofs.NamedRuntime.stateBefore_other S ρ hev v hu]
              exact ih


/-- **Premise (ii) at a store** (PROTOCOL.md#the-complete-protocol): an honest
tree holds at most one slot-`s` block.

This is the form the view-merge argument reads — `goldfish_vote`'s merge loop
ranges over *every* slot-`s` block of `Σ.T`, and the counterexample turns
exactly on two honest voters holding different such sets. Here the set is a
singleton at every honest store, so the loop's ranging over a set rather than
over "the" block costs nothing. -/
theorem unique_slot_block_in_store_core (S : Setup V) {ρ : Run V}
    (hadm : AdmissibleCore S ρ)
    {s : Slot} (hpos : 0 < s) (hprop : S.E.proposer s ∈ ρ.honest)
    {v w : V} {m n : Nat} {B B' : Block V}
    (hB : B ∈ (ρ.stateBefore S m v).st.core.T) (hB' : B' ∈ (ρ.stateBefore S n w).st.core.T)
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' := by
  have hproc : ∀ (x : V) (k : Nat) (C : Block V), C ∈ (ρ.stateBefore S k x).st.core.T →
      C.slot = s → ∃ D : NamedBlock V, D.erase = C ∧
        ∃ u : Time, Run.processes S ρ x (Object.block D) u := by
    intro x k C hC hCs
    obtain ⟨D, hDmem, hDerase⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S ρ k x hC
    rcases Proofs.Bridges.processes_block_of_mem_T S ρ x k D hDmem with rfl | ⟨-, e, -, -, hpr⟩
    · exact absurd hpos (by
        rw [← hCs, ← hDerase, show (NamedBlock.genesis : NamedBlock V).erase = Block.genesis
          from rfl, show Block.genesis.slot = 0 from rfl]
        exact Nat.lt_irrefl _)
    · exact ⟨D, hDerase, e.time, hpr⟩
  have hfield : ∀ (x : V) (k : Nat) (C : Block V), C ∈ (ρ.stateBefore S k x).st.core.T →
      C.slot = s → C.proposer? = some (S.E.proposer s) := by
    intro x k C hC hCs
    rcases proposerOk_stateBefore S ρ x k C hC with rfl | hp
    · exact absurd hpos (by
        rw [← hCs, show Block.genesis.slot = 0 from rfl]
        exact Nat.lt_irrefl _)
    · rw [← hCs]
      exact hp
  obtain ⟨D, hDerase, s₁, hp₁⟩ := hproc v m B hB hBs
  obtain ⟨D', hD'erase, s₂, hp₂⟩ := hproc w n B' hB' hB's
  have hDs : D.slot = s := by rw [← Proofs.NamedWire.erase_slot, hDerase, hBs]
  have hD's : D'.slot = s := by rw [← Proofs.NamedWire.erase_slot, hD'erase, hB's]
  have hDp : D.proposer? = some (S.E.proposer s) := by
    rw [← Proofs.NamedWire.erase_proposer, hDerase]; exact hfield v m B hB hBs
  have hD'p : D'.proposer? = some (S.E.proposer s) := by
    rw [← Proofs.NamedWire.erase_proposer, hD'erase]; exact hfield w n B' hB' hB's
  have hDeq : D = D' := unique_slot_block_core S hadm hprop hp₁ hp₂ hDp hD'p hDs hD's
  rw [← hDerase, ← hD'erase, hDeq]

theorem unique_slot_block_in_store (S : Setup V) {ρ : Run V} (hadm : Admissible S ρ)
    {s : Slot} (hpos : 0 < s) (hprop : S.E.proposer s ∈ ρ.honest)
    {v w : V} {m n : Nat} {B B' : Block V}
    (hB : B ∈ (ρ.stateBefore S m v).st.core.T)
    (hB' : B' ∈ (ρ.stateBefore S n w).st.core.T)
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' :=
  unique_slot_block_in_store_core S hadm.toNamedAdmissibleCore hpos hprop
    hB hB' hBs hB's

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
