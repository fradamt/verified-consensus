module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The tick, as a store property sees it (PROTOCOL.md#the-complete-protocol)

`Protocol.on_tick` is five branches over one store, each reading the store as
mutated so far (modeling-choices row 6). A property that survives the clock write
and each of the five duties therefore survives the tick, and the proof is the
same nest walk every time — so it is done once. -/

/-! ### `Σ.T` only grows (PROTOCOL.md#the-complete-protocol)

"Nothing is ever removed from `Σ.T`" — `on_block` is its only writer and it
inserts. The run-level form is what §3 needs: a block a store held at one instant
it still holds at every later one. -/


/-- **`Σ.T` only grows along a run** (PROTOCOL.md#the-complete-protocol). One induction over
the event list: `World.step` reaches `v`'s entry only at `v`'s own events, a
delivery is one handler and a tick is one `on_tick`, and none of them removes a
block. -/
theorem stateBefore_T_subset (S : Setup V) (ρ : Run V) (v : V) {i : Nat} :
    ∀ j : Nat, i ≤ j → (ρ.stateBefore S i v).st.T ⊆ (ρ.stateBefore S j v).st.T := by
  intro j hij B hB
  have hTi : (ρ.stateBefore S i v).st.core.T =
      (ρ.stateBefore S i v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBefore_invariants S ρ i v).1.1.1.1
  have hTj : (ρ.stateBefore S j v).st.core.T =
      (ρ.stateBefore S j v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBefore_invariants S ρ j v).1.1.1.1
  have hB' : B ∈ (ρ.stateBefore S i v).st.core.T := hB
  rw [hTi] at hB'
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB'
  show B ∈ (ρ.stateBefore S j v).st.core.T
  rw [hTj]
  exact Finset.mem_image.mpr
    ⟨D, NamedBodyRetention.stateBefore_bodies_mono S ρ v hij hD, hDB⟩




omit [Fintype V] [DecidableEq V] in
/-- §5.3 the height a finality pair carries is the head chain state's own
(PROTOCOL.md#the-complete-protocol). -/
theorem finality_pair_height {Λ : Record} {h_j : Height} {J : BlockId}
    {h_F h : Height} {T : BlockId}
    (hp : Protocol.finality_pair Λ h_j J h_F = some ⟨h, T⟩) : h_j = h := by
  simp only [Protocol.finality_pair] at hp
  split_ifs at hp
  simp_all

/-- §6.5 the finality pair `round_action` emits is `finality_pair` at the §6 head
(PROTOCOL.md#the-complete-protocol). Definitional: the duty threads the record through the
two rules and returns the second one's pair. -/
theorem round_action_finality_pair (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    ∃ Hd : Block V,
      Hd = Protocol.get_head_with contract E hc st (st.pool st.s)
        ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s ∧
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
        Protocol.finality_pair record.legacy
          (st.σ Hd).h_j (st.σ Hd).J.root (st.σ Hd).h_F :=
  ⟨_, rfl, rfl⟩

/- Kept for retained erased action-head consumers. -/
theorem round_action_head_mem_frame
    (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.Store V) (record : Protocol.NamedRecord)
    (hJ : st.J ∈ st.T) (hF : st.F ∈ st.T)
    {h : Height} {T : BlockId}
    (hp : (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract cache) E hc nd st.toHealing record).2.finality_pair =
      some ⟨h, T⟩) :
    ∃ Hd ∈ st.T, (st.σ Hd).h_j = h := by
  obtain ⟨Hd, hHd, heq⟩ :=
    round_action_finality_pair (DecoupledConsensusModel.Protocol.frameContract cache) E hc nd
      st.toHealing record
  have hp' : Protocol.finality_pair record.legacy (st.toHealing.σ Hd).h_j
      (st.toHealing.σ Hd).J.root (st.toHealing.σ Hd).h_F = some ⟨h, T⟩ := by
    rw [← heq]
    exact hp
  refine ⟨Hd, ?_, finality_pair_height hp'⟩
  rw [hHd]
  apply NamedProposalParent.runtime_get_head_mem cache E hc st.toHealing _ _ _
  change (if st.h_max = st.h_j + 1 then st.J else st.F) ∈ st.T
  split_ifs <;> assumption











end Proofs
end DecoupledConsensusModel

end
