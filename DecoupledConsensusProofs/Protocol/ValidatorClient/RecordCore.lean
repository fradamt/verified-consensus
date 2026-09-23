module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock record_attestation
  create_attestation finality_pair)
open Proofs.Records (LockCompatible)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. `Λ.target` is write-once (PROTOCOL.md#the-complete-protocol) -/


omit [DecidableEq V] [Fintype V] in
/-- **A released target is recorded** (PROTOCOL.md#the-complete-protocol), given that the
height was fresh or already held the same target — which is exactly what
`height_pair_target_compat` below establishes for every row that can emit. -/
theorem record_attestation_target_recorded (Λ : Record) (a : CombinedAttestation V)
    {h : Height} {T : BlockId} (hhp : a.height_pair = HeightPair.target h T)
    (hpre : Λ.target h = none ∨ Λ.target h = some T) :
    (record_attestation Λ a).target h = some T := by
  simp only [record_attestation, hhp]
  rcases hpre with hpre | hpre <;> cases a.finality_pair <;>
    simp_all [Record.with_lock, Record.with_target]

/-! ## 2. The effective lock is target-compatible (PROTOCOL.md#the-complete-protocol) -/


/-- **The lock `height_pair` reads has an empty or matching target record**
(PROTOCOL.md#the-complete-protocol).

Both arms are covered by different facts. The finality-pair override uses
`finality_pair_target_compatible`, which permits an empty target entry under
Rule B. The stored-lock arm uses `LockCompatible`. -/
theorem own_lock_compatible {Λ : Record} (hla : LockCompatible Λ) {h_j : Height}
    {J : BlockId} {h_F : Height} {h : Height} {X : BlockId}
    (hol : own_lock Λ h (finality_pair Λ h_j J h_F) = some X) :
    Λ.target h = none ∨ Λ.target h = some X := by
  cases hfp : finality_pair Λ h_j J h_F with
  | none =>
    rw [hfp] at hol
    exact (hla h X hol).2
  | some p =>
    rw [hfp] at hol
    simp only [own_lock] at hol
    split at hol
    · rename_i hph
      simp only [Option.some_inj] at hol
      subst hol
      rw [← hph]
      exact finality_pair_target_compatible hfp
    · exact (hla h X hol).2

/-! ## 3. The core (`the design` §9 L4, honest half) -/

/-- **Every emitting row agrees with the recorded entry**
(PROTOCOL.md#the-complete-protocol).

`height_pair` emits `.target h T` only when the height is fresh or already
recorded at `T`. Row by row: the lock row through `own_lock_recorded`, the
target-repeat row by its own equality test, and the no-history row because the
entry is `⊥` there. The three timeout rows and the empty row emit no target at
all. -/
theorem height_pair_target_compat {Λ : Record} (hla : LockCompatible Λ)
    {fields : Option (Height × BlockId × Bool)} {h_j : Height} {J : BlockId}
    {h_F : Height} {h : Height} {T : BlockId}
    (hp : height_pair Λ fields (finality_pair Λ h_j J h_F) =
      HeightPair.target h T) :
    Λ.target h = none ∨ Λ.target h = some T := by
  cases fields with
  | none => simp [height_pair] at hp
  | some f =>
    obtain ⟨h_c, T_c, ν⟩ := f
    obtain ⟨hh, hT⟩ := height_pair_target_height hp
    subst hh
    subst hT
    simp only [height_pair] at hp
    split at hp
    · exact absurd hp (by simp)
    · cases hol : own_lock Λ h (finality_pair Λ h_j J h_F) with
      | some X =>
        simp only [hol] at hp
        split at hp
        · rename_i heq
          subst heq
          exact own_lock_compatible hla hol
        · exact absurd hp (by simp)
      | none =>
        simp only [hol] at hp
        cases hs : Λ.target h with
        | some s =>
          simp only [hs] at hp
          split at hp
          · rename_i heq
            exact Or.inr (by rw [heq])
          · exact absurd hp (by simp)
        | none => exact Or.inl rfl


omit [DecidableEq V] [Fintype V] in
/-- **A released target is recorded before release**
(`the design` §9 L4, honest half; PROTOCOL.md#the-complete-protocol "record, then
release").

The half of clause (e) that looks forwards: after the emission the height is
recorded at exactly the target that was emitted, so the previous lemma applies
to every later attestation. -/
theorem create_attestation_saves (Λ : Record) (hla : LockCompatible Λ) (val_index : V)
    (r : Round) (confirmed : Option BlockId)
    (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId)
    (h_F : Height) {h : Height} {T : BlockId}
    (hhp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
      HeightPair.target h T) :
    (create_attestation Λ val_index r confirmed fields h_j J h_F).1.target h = some T := by
  simp only [create_attestation] at hhp ⊢
  exact record_attestation_target_recorded _ _ hhp (height_pair_target_compat hla hhp)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
