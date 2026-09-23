module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase

@[expose] public section

/-!
# A recorded target row is the reader's own earlier emission

`CanonicalTargetHistoryAt` and `CanonicalTimeoutHistoryAt` speak about the rows
sitting in an honest reader's lock record at a round read. The record is the
validator's OWN — `record_attestation` is its only writer, and it runs only
inside that validator's own tick (`World.step`'s tick branch; a delivery writes
the store alone). So a row is never something a Byzantine author put there:
it is the reader's own earlier attestation, and the moving history already
bounds what an honest attestation may carry.

This module is the run-level bridge. One step of the record is
`record_attestation`, whose target write is guarded by "only if the row is
empty", so a row present after a tick was either present before it or written
by that tick's own attestation. The induction over the event list lifts that
to: a row at any index was written by an emission at a strictly earlier index.

**Named runtime.** The signing state a node carries is now a
`Protocol.NamedRecord`, whose `legacy` field is the unchanged §5.3 record;
the anti-slashing rows are therefore read as `.Λ.legacy.target` and
`.Λ.legacy.timeout`. The emitted object carries a `NamedAttestation`, whose
`height_pair` is a `NamedHeightPair`, so every row equation is stated after
`.erase`. The tick itself is `Execution.NamedNode.tick`, taking one
`NodeState` rather than a store and a record separately, and the record steps
of the induction are the ones `Protocol.RecordTargetHistoryRun` and
`RecordFreshRun` already restated (`on_tick_emit_target_introduced`,
`on_tick_emit_timeout_introduced`, `target_mono_on_tick_emit`).

The action's own row is read through the named duty: `roundActionRow_*_source`
speak about `Protocol.NamedActions.round_action_with` at the action's grade
contract, and the run-level source identity is
`NamedActionSources.action_source`/`action_witness`, which name the FG source
`actionFGSource` and its retained full body with the stored
`Protocol.derive_named` derivation. `derive_named` has no bridge to the
retired `derived_state`, so the two fold conclusions are stated over
`NamedBlock` witnesses and the same-height target agreement is
`Proofs.NamedEntryHeight.entry_eq_on_plateau` over named ancestry.

Both endpoint theorems carry `MovingChainHistoryRun`'s pinned hypothesis
`_of_selectedG2_preceq_honestPreviousCarrier` (PRE-BUILDING): its producer
`SGOutputInheritanceRun.honestSupporter_of_nodeQ2` is outside this module's
import cone and needs the round's relative-carrier window and grade-forming
majority, which this statement does not carry.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]





/-- **A recorded target row was written by the reader's own earlier tick.** -/
theorem stateBefore_target_own_emission
    (S : Setup V) (rho : Run V) (v : V) {h : Height} {X : BlockId} :
    ∀ i : Nat, (rho.stateBefore S i v).Λ.legacy.target h = some X →
      ∃ (j : Nat) (t : Time),
        j < i ∧ rho.events[j]? = some (Event.tick v t) ∧
        ∃ a : NamedAttestation V,
          Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S j v) t).2 ∧
            a.erase.height_pair = HeightPair.target h X := by
  intro i hrow
  obtain ⟨j, hj, t, a, hjev, hmem, hpair⟩ :=
    Protocol.recordTarget_emission_before S rho v i hrow
  exact ⟨j, t, hj, hjev, a, hmem, hpair⟩

/-! ## The timeout row, the same way

`record_attestation_timeout_introduced` (RecordFreshRun) is already the record
step's backward direction, so only the tick and the run induction are new. -/

/-- **One tick, backwards, at a timeout row.** -/
theorem timeout_row_of_on_tick_emit
    (S : Setup V) (v : V) (n : NodeState V) (t : Time) {h : Height}
    (hrow : (on_tick_emit S v n t).1.record.legacy.timeout h = true) :
    n.Λ.legacy.timeout h = true ∨
      (n.Λ.legacy.timeout h = false ∧
        ∃ a : NamedAttestation V,
          Object.attest a ∈ (on_tick_emit S v n t).2 ∧
            a.erase.height_pair = HeightPair.timeout h) := by
  cases hpre : n.Λ.legacy.timeout h with
  | true => exact Or.inl rfl
  | false =>
      exact Or.inr ⟨rfl, on_tick_emit_timeout_introduced S v n t hpre hrow⟩

/-- **A recorded timeout row was written by the reader's own earlier tick.** -/
theorem stateBefore_timeout_own_emission
    (S : Setup V) (rho : Run V) (v : V) {h : Height} :
    ∀ i : Nat, (rho.stateBefore S i v).Λ.legacy.timeout h = true →
      ∃ (j : Nat) (t : Time),
        j < i ∧ rho.events[j]? = some (Event.tick v t) ∧
        (rho.stateBefore S j v).Λ.legacy.timeout h = false ∧
        ∃ a : NamedAttestation V,
          Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S j v) t).2 ∧
            a.erase.height_pair = HeightPair.timeout h := by
  intro i
  induction i with
  | zero =>
      intro hrow
      exact absurd hrow (by
        simp [Run.stateBefore, NamedRun.stateBefore, List.take_zero, List.foldl_nil,
          NamedWorld.init, NamedNode.initial, Protocol.NamedRecord.initial,
          Record.initial])
  | succ i ih =>
      intro hrow
      have hstep : rho.stateBefore S (i + 1) =
          (rho.events[i]?.toList).foldl (World.step S) (rho.stateBefore S i) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hev : rho.events[i]? with _ | ev
      · rw [hstep, hev] at hrow
        simp only [Option.toList, List.foldl_nil] at hrow
        obtain ⟨j, t, hji, hjev, hf, ha⟩ := ih hrow
        exact ⟨j, t, hji.trans (Nat.lt_succ_self i), hjev, hf, ha⟩
      · cases ev with
        | tick u t =>
            by_cases hu : u = v
            · subst hu
              have hpost :
                  (on_tick_emit S u (rho.stateBefore S i u) t).1.record.legacy.timeout h
                    = true := by
                rw [← stateBefore_succ_record S rho hev]
                exact hrow
              rcases timeout_row_of_on_tick_emit S u (rho.stateBefore S i u) t hpost with
                hpre | ⟨hfalse, a, hmem, hhp⟩
              · obtain ⟨j, t', hji, hjev, hf, ha⟩ := ih hpre
                exact ⟨j, t', hji.trans (Nat.lt_succ_self i), hjev, hf, ha⟩
              · exact ⟨i, t, Nat.lt_succ_self i, hev, hfalse, a, hmem, hhp⟩
            · rw [hstep, hev] at hrow
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step,
                Function.update_of_ne (Ne.symm hu)] at hrow
              obtain ⟨j, t', hji, hjev, hf, ha⟩ := ih hrow
              exact ⟨j, t', hji.trans (Nat.lt_succ_self i), hjev, hf, ha⟩
        | deliver u o t =>
            by_cases hu : u = v
            · subst hu
              rw [hstep, hev] at hrow
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_self] at hrow
              rw [process_record] at hrow
              obtain ⟨j, t', hji, hjev, hf, ha⟩ := ih hrow
              exact ⟨j, t', hji.trans (Nat.lt_succ_self i), hjev, hf, ha⟩
            · rw [hstep, hev] at hrow
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step,
                Function.update_of_ne (Ne.symm hu)] at hrow
              obtain ⟨j, t', hji, hjev, hf, ha⟩ := ih hrow
              exact ⟨j, t', hji.trans (Nat.lt_succ_self i), hjev, hf, ha⟩

/-! ## The emitted row names the action's own finality-gadget source

`RowFreshnessRun.honestRow_height_le_source` reads the HEIGHT off the row. The
target history needs the row's TARGET ROOT as well, and it is the same field
tuple: the named round action builds its height pair from the one shared
attestation read, whose `fields` are `(σ Q).h, (σ Q).T_h.root, (σ Q).nj` at the
source `Q`, so a target row names that source's height and target root
together. -/



/-! ## The post-boundary target history

A row at a height ABOVE the boundary frontier was emitted after the boundary
(`honestRow_after_frontier`), so the four pieces compose: the row is the
reader's own emission, that emission is its round's action attestation, the
attestation's row names the action's own source with the row's height and
target root, and the fold puts that source below its endpoint. -/


/-- **The row bundle's slot field is met at the record's own endpoint index.**

`opening_slot m = m * R` and `R ≥ 2`, so a round strictly below `r` has its
opening slot at least two slots below `opening_slot r`. This is what makes the
`hdata` range satisfiable at `e:= opening_slot r`, the index the finality
records state their history fields at: the rows an honest reader holds at the
round-`r` action were written by actions at rounds strictly below `r`, so their
sources are bounded two slots below the round's own opening. -/
theorem openingSlot_add_two_le_openingSlot_of_lt
    (S : Setup V) {m r : Round} (h : m < r) :
    S.hc.opening_slot m + 2 ≤ S.hc.opening_slot r := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hstep : (m + 1) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ h
  simp only [Protocol.HealConfig.opening_slot]
  calc
    m * S.hc.R + 2 ≤ m * S.hc.R + S.hc.R := Nat.add_le_add_left hR _
    _ = (m + 1) * S.hc.R := by ring
    _ ≤ r * S.hc.R := hstep



omit [DecidableEq V] [Fintype V] in
/-- **The three ways a timeout pair is emitted**, with the repeat case excluded.

Reading `Protocol.height_pair` backwards: with the record's own timeout
still false, an emitted timeout at height `h` means the fields are the source's
own at that height, and either the source carries the no-justification flag, or
the record already holds a DIFFERENT target at `h`. -/
theorem height_pair_timeout_cases {Λ : Record}
    {fields : Option (Height × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Height}
    (hpre : Λ.timeout h = false)
    (hp : Protocol.height_pair Λ fields fp = HeightPair.timeout h) :
    ∃ (T : BlockId) (nu : Bool), fields = some (h, T, nu) ∧
      (nu = true ∨ ∃ recorded : BlockId,
        Λ.target h = some recorded ∧ recorded ≠ T) := by
  cases hf : fields with
  | none =>
      rw [hf] at hp
      simp only [Protocol.height_pair, reduceCtorEq] at hp
  | some f =>
      obtain ⟨h_c, T_c, nu⟩ := f
      rw [hf] at hp
      simp only [Protocol.height_pair] at hp
      by_cases htimeout : Λ.timeout h_c = true
      · rw [if_pos htimeout] at hp
        have hhc : h_c = h := by
          simpa only [HeightPair.timeout.injEq] using hp
        subst hhc
        rw [hpre] at htimeout
        exact absurd htimeout (by simp)
      · rw [if_neg htimeout] at hp
        cases hlock : Protocol.own_lock Λ h_c fp with
        | some locked =>
            rw [hlock] at hp
            dsimp only at hp
            by_cases hleq : locked = T_c
            · rw [if_pos hleq] at hp
              simp only [reduceCtorEq] at hp
            · rw [if_neg hleq] at hp
              simp only [reduceCtorEq] at hp
        | none =>
            rw [hlock] at hp
            dsimp only at hp
            cases htar : Λ.target h_c with
            | some recorded =>
                rw [htar] at hp
                dsimp only at hp
                by_cases hreq : recorded = T_c
                · rw [if_pos hreq] at hp
                  simp only [reduceCtorEq] at hp
                · rw [if_neg hreq] at hp
                  have hhc : h_c = h := by
                    simpa only [HeightPair.timeout.injEq] using hp
                  subst hhc
                  exact ⟨T_c, nu, rfl, Or.inr ⟨recorded, htar, hreq⟩⟩
            | none =>
                rw [htar] at hp
                dsimp only at hp
                by_cases hnu : nu = true
                · rw [if_pos hnu] at hp
                  have hhc : h_c = h := by
                    simpa only [HeightPair.timeout.injEq] using hp
                  subst hhc
                  exact ⟨T_c, nu, rfl, Or.inl hnu⟩
                · rw [if_neg hnu] at hp
                  simp only [reduceCtorEq] at hp



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms stateBefore_target_own_emission
#print axioms timeout_row_of_on_tick_emit
#print axioms stateBefore_timeout_own_emission
#print axioms openingSlot_add_two_le_openingSlot_of_lt
#print axioms height_pair_timeout_cases
end DecoupledConsensusModel.Proofs.HealingSurface

end
