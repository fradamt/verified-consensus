module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# Low finality-pair and record core

Pure record facts and the exact Section 6 action projection used by the recurring
finality layer.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record create_attestation finality_pair height_pair own_lock
  record_attestation)
open Protocol (HealConfig)
open Proofs.Records (LockCompatible)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `target` only grows through `record_attestation`. -/
theorem record_attestation_target_mono (Λ : Record) (a : CombinedAttestation V)
    {h : Height} {T : BlockId} (hs : Λ.target h = some T) :
    (record_attestation Λ a).target h = some T := by
  have key : ∀ Λ' : Record, Λ'.target h = some T →
      (match a.height_pair with
        | HeightPair.empty => Λ'
        | HeightPair.timeout g => Λ'.with_timeout g
        | HeightPair.target g X =>
          if Λ'.target g = none then Λ'.with_target g X else Λ').target h = some T := by
    intro Λ' hs'
    cases a.height_pair with
    | empty => exact hs'
    | timeout g => exact hs'
    | target g X =>
      change (if Λ'.target g = none then Λ'.with_target g X else Λ').target h = some T
      by_cases hg : Λ'.target g = none
      · rw [if_pos hg]
        simp only [Record.with_target]
        by_cases hgh : h = g
        · subst hgh
          rw [hg] at hs'
          exact absurd hs' (by simp)
        · simp only [if_neg hgh]
          exact hs'
      · rw [if_neg hg]
        exact hs'
  simp only [record_attestation]
  cases a.finality_pair with
  | none => exact key Λ hs
  | some p => exact key (Λ.with_lock p.height p.target) hs

/-- A nonempty finality pair has an empty or matching target record. -/
theorem finality_pair_target_compatible {Λ : Record} {h_j : Height} {J : BlockId}
    {h_F : Height} {p : FinalityPair} (h : finality_pair Λ h_j J h_F = some p) :
    Λ.target p.height = none ∨ Λ.target p.height = some p.target := by
  simp only [finality_pair] at h
  split at h
  · split at h
    · rename_i hguard
      simp only [Option.some_inj] at h
      subst h
      exact hguard.1
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq V] [Fintype V] in
/-- A nonempty finality pair exposes all three record conditions at its
height. -/
theorem finality_pair_record_conditions {Λ : Record} {h_j : Height}
    {J : BlockId} {h_F : Height} {p : FinalityPair}
    (h : finality_pair Λ h_j J h_F = some p) :
    Λ.timeout p.height = false ∧
      (Λ.target p.height = none ∨ Λ.target p.height = some p.target) ∧
      (Λ.lock p.height = none ∨ Λ.lock p.height = some p.target) := by
  simp only [finality_pair] at h
  split at h
  · split at h
    · rename_i hguard
      simp only [Option.some_inj] at h
      subst h
      exact ⟨hguard.2.1, hguard.1, hguard.2.2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq V] [Fintype V] in
/-- The height-pair fold leaves the lock written by the finality pair unchanged. -/
theorem record_attestation_lock_eq (Λ : Record) (a : CombinedAttestation V)
    (g : Height) :
    (record_attestation Λ a).lock g =
      (match a.finality_pair with
        | some p => Λ.with_lock p.height p.target
        | none => Λ).lock g := by
  simp only [record_attestation]
  have key : ∀ Λ' : Record,
      (match a.height_pair with
        | HeightPair.empty => Λ'
        | HeightPair.timeout k => Λ'.with_timeout k
        | HeightPair.target k Y =>
          if Λ'.target k = none then Λ'.with_target k Y else Λ').lock g = Λ'.lock g := by
    intro Λ'
    cases a.height_pair with
    | empty => rfl
    | timeout k => rfl
    | target k Y =>
      change (if Λ'.target k = none then Λ'.with_target k Y else Λ').lock g = Λ'.lock g
      by_cases hk : Λ'.target k = none
      · rw [if_pos hk]
        rfl
      · rw [if_neg hk]
  cases a.finality_pair with
  | none => exact key Λ
  | some p => exact key (Λ.with_lock p.height p.target)

omit [DecidableEq V] [Fintype V] in
/-- The lock stored by `record_attestation` is the lock that the same
attestation's height-pair rule reads. -/
theorem record_attestation_lock_eq_own_lock (Λ : Record)
    (a : CombinedAttestation V) (g : Height) :
    (record_attestation Λ a).lock g = own_lock Λ g a.finality_pair := by
  rw [record_attestation_lock_eq]
  cases a.finality_pair with
  | none => rfl
  | some p =>
      by_cases h : p.height = g
      · subst g
        simp [own_lock, Record.with_lock]
      · simp [own_lock, Record.with_lock, h, Ne.symm h]

omit [DecidableEq V] [Fintype V] in
/-- A height-pair rule cannot emit a timeout at a height where its effective
lock is present and the timeout bit is clear. -/
theorem height_pair_ne_timeout_of_own_lock {Λ : Record}
    {fields : Option (Height × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Height} {T : BlockId} (htimeout : Λ.timeout h = false)
    (hlock : own_lock Λ h fp = some T) :
    height_pair Λ fields fp ≠ HeightPair.timeout h := by
  intro hp
  have hheight : (height_pair Λ fields fp).height? = some h := by
    rw [hp]
    rfl
  obtain ⟨X, nu, hfields⟩ := Proofs.Engine.height_pair_height_gated hheight
  rw [hfields] at hp
  simp only [height_pair, htimeout, Bool.false_eq_true, ↓reduceIte, hlock] at hp
  split at hp <;> simp_all

omit [DecidableEq V] [Fintype V] in
/-- At a locked height, every target row equals the effective lock. -/
theorem height_pair_target_eq_of_own_lock {Λ : Record}
    {fields : Option (Height × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Height} {T U : BlockId} (htimeout : Λ.timeout h = false)
    (hlock : own_lock Λ h fp = some T)
    (hp : height_pair Λ fields fp = HeightPair.target h U) : U = T := by
  obtain ⟨nu, hfields⟩ := Proofs.Engine.height_pair_target_gated hp
  rw [hfields] at hp
  simp only [height_pair, htimeout, Bool.false_eq_true, ↓reduceIte, hlock] at hp
  split at hp
  · rename_i heq
    exact heq.symm
  · contradiction

omit [DecidableEq V] [Fintype V] in
/-- A record update preserves an empty-or-matching target entry when every
target row at that height matches the lock. -/
theorem record_attestation_target_compatible_of
    (Λ : Record) (a : CombinedAttestation V) {h : Height} {T : BlockId}
    (hpre : Λ.target h = none ∨ Λ.target h = some T)
    (hrow : ∀ U, a.height_pair = HeightPair.target h U → U = T) :
    (record_attestation Λ a).target h = none ∨
      (record_attestation Λ a).target h = some T := by
  rcases hpre with hnone | hsome
  · cases hhp : a.height_pair with
    | empty =>
        cases hfp : a.finality_pair <;>
          exact Or.inl (by
            simpa [record_attestation, hhp, hfp, Record.with_lock] using hnone)
    | timeout g =>
        cases hfp : a.finality_pair <;>
          exact Or.inl (by
            simpa [record_attestation, hhp, hfp, Record.with_lock,
              Record.with_timeout] using hnone)
    | target g U =>
        by_cases hgh : g = h
        · subst g
          have hUT : U = T := hrow U hhp
          subst U
          cases hfp : a.finality_pair <;>
            exact Or.inr (by
              simp [record_attestation, hhp, hfp, Record.with_lock,
                Record.with_target, hnone])
        · have hhg : h ≠ g := Ne.symm hgh
          cases hfp : a.finality_pair <;> exact Or.inl (by
            simp only [record_attestation, hhp, hfp]
            split <;>
              simpa [Record.with_lock, Record.with_target, hhg] using hnone)
  · exact Or.inr (record_attestation_target_mono Λ a hsome)

omit [DecidableEq V] [Fintype V] in
/-- A record update preserves a clear timeout bit unless it emits the exact
timeout row. -/
theorem record_attestation_timeout_false_of_ne {Λ : Record}
    (a : CombinedAttestation V) {h : Height}
    (hpre : Λ.timeout h = false)
    (hne : a.height_pair ≠ HeightPair.timeout h) :
    (record_attestation Λ a).timeout h = false := by
  cases hhp : a.height_pair with
  | empty =>
      cases hfp : a.finality_pair <;>
        simpa [record_attestation, hhp, hfp, Record.with_lock] using hpre
  | timeout g =>
      have hgh : g ≠ h := by
        intro heq
        subst g
        exact hne hhp
      have hhg : h ≠ g := Ne.symm hgh
      cases hfp : a.finality_pair <;>
        simpa [record_attestation, hhp, hfp, Record.with_lock,
          Record.with_timeout, hhg] using hpre
  | target g X =>
      cases hfp : a.finality_pair <;>
        simp only [record_attestation, hhp, hfp] <;> split <;>
          simpa [Record.with_lock, Record.with_target] using hpre

omit [DecidableEq V] [Fintype V] in
/-- `LockCompatible` is preserved by the single record writer. -/
theorem lockCompatible_create_attestation {Λ : Record} (hla : LockCompatible Λ)
    (val_index : V) (r : Round) (confirmed : Option BlockId)
    (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId)
    (h_F : Height) :
    LockCompatible (create_attestation Λ val_index r confirmed fields h_j J h_F).1 := by
  intro g X hlock
  simp only [create_attestation] at hlock ⊢
  let fp := finality_pair Λ h_j J h_F
  let hp := height_pair Λ fields fp
  let a : CombinedAttestation V := ⟨val_index, r, confirmed, hp, fp⟩
  change (record_attestation Λ a).lock g = some X at hlock
  change (record_attestation Λ a).timeout g = false ∧
    ((record_attestation Λ a).target g = none ∨
      (record_attestation Λ a).target g = some X)
  have hol : own_lock Λ g fp = some X := by
    rw [← record_attestation_lock_eq_own_lock Λ a g]
    exact hlock
  have hpre : Λ.timeout g = false ∧
      (Λ.target g = none ∨ Λ.target g = some X) := by
    cases hfp : finality_pair Λ h_j J h_F with
    | none =>
        have hol' : Λ.lock g = some X := by simpa [fp, hfp, own_lock] using hol
        exact hla g X hol'
    | some p =>
        by_cases hpg : p.height = g
        · have hcond := finality_pair_record_conditions hfp
          have hpX : p.target = X := by
            have hol' : some p.target = some X := by
              simpa [fp, hfp, own_lock, hpg] using hol
            exact Option.some_inj.mp hol'
          subst X
          exact ⟨by simpa [hpg] using hcond.1,
            by simpa [hpg] using hcond.2.1⟩
        · have hol' : Λ.lock g = some X := by
            simpa [fp, hfp, own_lock, hpg] using hol
          exact hla g X hol'
  have hne : hp ≠ HeightPair.timeout g :=
    height_pair_ne_timeout_of_own_lock hpre.1 hol
  constructor
  · exact record_attestation_timeout_false_of_ne a hpre.1 (by simpa [a] using hne)
  · apply record_attestation_target_compatible_of Λ a hpre.2
    intro U hrow
    apply height_pair_target_eq_of_own_lock hpre.1 hol
    simpa [a] using hrow


omit [DecidableEq V] [Fintype V] in
/-- An existing compatible lock determines the effective lock read by the next
height-pair rule, including when the same attestation emits a finality pair. -/
theorem own_lock_eq_of_lock {Λ : Record} {h : Height} {T : BlockId}
    (hlock : Λ.lock h = some T)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    own_lock Λ h (finality_pair Λ h_j J h_F) = some T := by
  cases hfp : finality_pair Λ h_j J h_F with
  | none => simpa [own_lock] using hlock
  | some p =>
      by_cases hph : p.height = h
      · have hpTarget : p.target = T := by
          have hguard := (finality_pair_record_conditions hfp).2.2
          rw [hph, hlock] at hguard
          rcases hguard with hnone | hsame
          · contradiction
          · exact (Option.some_inj.mp hsame).symm
        simp [own_lock, hph, hpTarget]
      · simp [own_lock, hph, hlock]

omit [DecidableEq V] [Fintype V] in
/-- A valid `create_attestation` call cannot change an existing compatible
lock. -/
theorem create_attestation_lock_mono {Λ : Record} {h : Height} {T : BlockId}
    (hlock : Λ.lock h = some T)
    (val_index : V) (r : Round) (confirmed : Option BlockId)
    (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    (create_attestation Λ val_index r confirmed fields h_j J h_F).1.lock h =
      some T := by
  simp only [create_attestation]
  rw [record_attestation_lock_eq_own_lock]
  exact own_lock_eq_of_lock hlock h_j J h_F

/-- The resolved Goldfish head read by a round action under a grade contract. -/
def actionHeadWith (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (st : Protocol.HealingStore V) : Block V :=
  Protocol.get_head_with contract E hc st (st.pool st.s)
    ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s


/-- The resolved Goldfish head read by a round action. -/
noncomputable def actionHead (E : Env V) (hc : HealConfig) (st : Protocol.HealingStore V) : Block V :=
  Protocol.get_head_hc E hc st (st.pool st.s)
    ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
