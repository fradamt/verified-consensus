module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Ladder

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock record_attestation create_attestation)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. `own_lock` at the two heights (PROTOCOL.md#the-complete-protocol) -/

/-- At its own height the override wins: `own_lock` returns **this**
attestation's finality target, not the record's. -/
theorem own_lock_self (Λ : Record) (h : Height) (T : BlockId) :
    own_lock Λ h (some ⟨h, T⟩) = some T := by
  simp [own_lock]


/-! ## 2. The same-attestation half

All seven rows of `height_pair` name the height its fields carry, so the proof
below splits on whether that height is the finality pair's — the override's own
condition — and then on the rows. -/

/-- **One attestation never forms E1 evidence against itself**
(PROTOCOL.md#the-complete-protocol; `the design` §9 O-e).

When the height pair and the finality pair land at one height, the override
makes `height_pair` read the finality pair's own target, and the lock row emits
`.target` only when it matches. So the two targets agree — there is no E1
evidence inside a single attestation, whatever the head and the height source
did. -/
theorem height_pair_target_height {Λ : Record} {h_c h : Height}
    {T_c T : BlockId} {ν : Bool} {fp : Option FinalityPair}
    (hp : height_pair Λ (some (h_c, T_c, ν)) fp = HeightPair.target h T) :
    h = h_c ∧ T = T_c := by
  simp only [height_pair] at hp
  split at hp
  · exact absurd hp (by simp)
  · split at hp
    · split at hp
      · simp only [HeightPair.target.injEq] at hp
        exact ⟨hp.1.symm, hp.2.symm⟩
      · exact absurd hp (by simp)
    · split at hp
      · split at hp
        · simp only [HeightPair.target.injEq] at hp
          exact ⟨hp.1.symm, hp.2.symm⟩
        · exact absurd hp (by simp)
      · split at hp
        · exact absurd hp (by simp)
        · simp only [HeightPair.target.injEq] at hp
          exact ⟨hp.1.symm, hp.2.symm⟩

/-- **One attestation never forms E1 evidence against itself**
(PROTOCOL.md#the-complete-protocol; `the design` §9 O-e).

When the height pair and the finality pair land at one height, the override
makes `height_pair` read the finality pair's own target, and the lock row emits
`.target` only when it matches. So the two targets agree — there is no E1
evidence inside a single attestation, whatever the head and the height source
did. -/
theorem height_pair_no_self_E1 {Λ : Record}
    {fields : Option (Height × BlockId × Bool)} {h : Height} {T T' : BlockId}
    (hp : height_pair Λ fields (some ⟨h, T'⟩) = HeightPair.target h T) :
    T = T' := by
  cases fields with
  | none => simp [height_pair] at hp
  | some f =>
    obtain ⟨h_c, T_c, ν⟩ := f
    obtain ⟨hh, hT⟩ := height_pair_target_height hp
    subst hh
    subst hT
    simp only [height_pair, own_lock_self] at hp
    split at hp
    · exact absurd hp (by simp)
    · split at hp
      · rename_i heq
        exact heq.symm
      · exact absurd hp (by simp)

omit [DecidableEq V] [Fintype V] in
/-- **The same statement at `create_attestation`** (PROTOCOL.md#the-complete-protocol): the
attestation the validator releases carries no E1 evidence against itself. -/
theorem create_attestation_no_self_E1 (Λ : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T T' : BlockId}
    (hhp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
      HeightPair.target h T)
    (hfp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
      some ⟨h, T'⟩) :
    T = T' := by
  simp only [create_attestation] at hhp hfp
  rw [hfp] at hhp
  exact height_pair_no_self_E1 hhp

/-! ## 3. The cross-round half (PROTOCOL.md#the-complete-protocol) -/




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
