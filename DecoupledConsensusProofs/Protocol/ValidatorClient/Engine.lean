module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Weights
public import DecoupledConsensusModel.Protocol.ValidatorClient
public import DecoupledConsensusModel.Protocol.Duties.Proposals

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Engine

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## S1–S3 — vote selectivity (PROTOCOL.md#the-complete-protocol) -/



/-- **S3** (rev. 3 §1.2; PROTOCOL.md#the-complete-protocol): with `K ≥ 2`, a multiple of `K`
has no successor that is a multiple of `K`. -/
theorem not_dvd_succ_of_dvd {K H : Nat} (hK : 2 ≤ K) (h : K ∣ H) : ¬K ∣ (H + 1) := by
  intro hsucc
  have hone : K ∣ 1 := (Nat.dvd_add_right h).mp hsucc
  have := Nat.le_of_dvd Nat.one_pos hone
  omega

/-- **S3**, as the model reads it (PROTOCOL.md#the-complete-protocol): the height
after a periodic one is ordinary, so `nj` is false there whatever the finality
debt is.

This is why crossing a recovery height `H` on branch-agnostic timeout votes buys
the adversary nothing above it: at `H + 1` an honest validator takes
`height_pair`'s adopt branch and emits an exact — hence branch-selective (S2) —
pair. -/
theorem nonjustifiable_succ_of_dvd (cfg : HeightConfig) {H : Height} (h : cfg.K ∣ H)
    (h_F : Height) : Protocol.nonjustifiable cfg (H + 1) h_F = false := by
  simp only [Protocol.nonjustifiable, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact Or.inl (not_dvd_succ_of_dvd cfg.K_ge_two h)



section Gating

variable {Λ : Record}

omit [Fintype V] [DecidableEq V] in
/-- §5.3 `height_pair` emits one of exactly three things, and the two nonempty
ones both read the caller's own height fields (PROTOCOL.md#the-complete-protocol).

**This is Lemma G1's whole content.** All seven rows of the figure's table
produce `(⊥,⊥)`, `(h_c, ⊥)` or `(h_c, T_c)`; no row invents a height and no row
invents a target. Everything else about G1 is bookkeeping about where the caller
got `(h_c, T_c)` from, and that is what the two duties below settle.

The fields arrive as one `Option`, so the `none` row — §6's "no fresh quorum, no
height pair" (PROTOCOL.md#the-complete-protocol) — is the first disjunct. -/
theorem height_pair_cases (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) :
    Protocol.height_pair Λ fields fp = .empty ∨
      ∃ (h : Height) (T : BlockId) (ν : Bool), fields = some (h, T, ν) ∧
        (Protocol.height_pair Λ fields fp = .timeout h ∨
          Protocol.height_pair Λ fields fp = .target h T) := by
  cases fields with
  | none => exact Or.inl rfl
  | some f =>
    obtain ⟨h, T, ν⟩ := f
    have key : Protocol.height_pair Λ (some (h, T, ν)) fp = .empty ∨
        Protocol.height_pair Λ (some (h, T, ν)) fp = .timeout h ∨
        Protocol.height_pair Λ (some (h, T, ν)) fp = .target h T := by
      dsimp only [Protocol.height_pair]
      repeat' split
      all_goals
        first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
    rcases key with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h, T, ν, rfl, h0⟩


omit [Fintype V] [DecidableEq V] in
/-- §5.3 G1 read off an emitted target pair (PROTOCOL.md#the-complete-protocol): the height
and the target are the caller's own. -/
theorem height_pair_target_gated {fields : Option (Height × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Height} {T : BlockId}
    (hp : Protocol.height_pair Λ fields fp = .target h T) :
    ∃ ν : Bool, fields = some (h, T, ν) := by
  rcases height_pair_cases (Λ := Λ) fields fp with hc | ⟨h', T', ν, hf, hc | hc⟩
  · exact absurd (hp ▸ hc) (by simp)
  · exact absurd (hc ▸ hp) (by simp)
  · obtain ⟨rfl, rfl⟩ := HeightPair.target.injEq .. ▸ (hc ▸ hp : _)
    exact ⟨ν, hf⟩

omit [Fintype V] [DecidableEq V] in
/-- §5.3 G1 read off an emitted nonempty pair (PROTOCOL.md#the-complete-protocol): the height
is the caller's own. -/
theorem height_pair_height_gated {fields : Option (Height × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Height}
    (hp : (Protocol.height_pair Λ fields fp).height? = some h) :
    ∃ (T : BlockId) (ν : Bool), fields = some (h, T, ν) := by
  rcases height_pair_cases (Λ := Λ) fields fp with hc | ⟨h', T', ν, hf, hc | hc⟩
  · rw [hc] at hp; exact absurd hp (by simp [HeightPair.height?])
  · rw [hc] at hp
    simp only [HeightPair.height?, Option.some_inj] at hp
    exact ⟨T', ν, hp ▸ hf⟩
  · rw [hc] at hp
    simp only [HeightPair.height?, Option.some_inj] at hp
    exact ⟨T', ν, hp ▸ hf⟩

end Gating

/-! ### G1 at the §5 duty (PROTOCOL.md#the-complete-protocol) -/




/-! ### G1 at the §6 duty (PROTOCOL.md#the-complete-protocol) -/

section GradedGate

omit [Fintype V] in
/-- The unique-choice picker returns a member of its own set
(`Substrate/Blocks.lean:223`). -/
theorem pickUnique?_mem {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {x : α} (h : pickUnique? T p = some x) : x ∈ T := by
  unfold pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact Finset.choose_mem _ _ hex
  · exact absurd h (by simp)

omit [Fintype V] in
/-- §1 "deepest" returns a member of the tree it ranges over
(PROTOCOL.md#the-complete-protocol). -/
theorem deepest?_mem {T : Finset (Block V)} {B : Block V}
    (h : Block.deepest? T = some B) : B ∈ T :=
  pickUnique?_mem h

omit [Fintype V] in
/-- §6.5 every member of `chain_up n B` is an ancestor of `B`
(PROTOCOL.md#the-complete-protocol). -/
theorem mem_chain_up_preceq : ∀ (n : Nat) (B X : Block V),
    X ∈ Protocol.chain_up n B → Block.preceq X B = true := by
  intro n
  induction n with
  | zero =>
      intro B X h
      simp only [Protocol.chain_up, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact Block.preceq_self _
  | succ n ih =>
      intro B X h
      cases B with
      | genesis =>
          simp only [Protocol.chain_up, Block.parent?, List.mem_cons, List.not_mem_nil,
            or_false] at h
          subst h
          exact Block.preceq_self _
      | node p s r gv gsv ats i =>
          simp only [Protocol.chain_up, Block.parent?, List.mem_cons] at h
          rcases h with rfl | h
          · exact Block.preceq_self _
          · simp only [Block.preceq, Bool.or_eq_true]
            exact Or.inr (ih p X h)

omit [Fintype V] in
/-- §6.5 `chain_of C` is `{B: B ⪯ C}` (PROTOCOL.md#the-complete-protocol). -/
theorem mem_chain_of_preceq {C X : Block V} (h : X ∈ Protocol.chain_of C) :
    Block.preceq X C = true :=
  mem_chain_up_preceq _ _ _ h

omit [Fintype V] in
/-- §6.5 `deepest_clear` ranges over a chain, so whatever it returns is an
ancestor of the block it was given (PROTOCOL.md#the-complete-protocol, F6.6). -/
theorem deepest_clear_preceq {floor : Option (Block V)} {C B : Block V}
    {test : Block V → Bool} (h : Protocol.deepest_clear floor C test = some B) :
    Block.preceq B C = true := by
  unfold Protocol.deepest_clear at h
  have hmem := deepest?_mem h
  exact mem_chain_of_preceq (List.mem_toFinset.mp (Finset.mem_filter.mp hmem).1)



open Protocol (GradeContract)




end GradedGate

/-! ## G4 — quorums need confirmed honest signers (PROTOCOL.md#the-complete-protocol) -/




omit [Fintype V] in
/-- E2 evidence at a pinned height is scoped slashability
(PROTOCOL.md#the-complete-protocol): the height and the two roots are forgotten. The
analogue of `Proofs.slashableBetween_of_e1EvidenceForPair`. -/
theorem slashableBetween_of_e2EvidenceAtHeight {h : Height} {T₁ T₂ : BlockId}
    {A₁ A₂ : Finset (CombinedAttestation V)} {i : V} (hne : T₁ ≠ T₂)
    (hev : E2EvidenceAtHeight h T₁ T₂ A₁ A₂ i) : SlashableBetween A₁ A₂ i := by
  obtain ⟨a, ha, b, hb, hav, hbv, hpa, hpb⟩ := hev
  refine ⟨a, ha, b, hb, hav, hbv, ?_⟩
  have hv : a.val_index = b.val_index := by rw [hav, hbv]
  have h2 : Protocol.e2Slashable a b = true := by
    simp [Protocol.e2Slashable, Protocol.sameValidator,
      Protocol.e2Fields, hpa, hpb, hv, hne]
  change Protocol.slashable a b = true
  simp only [Protocol.slashable, h2, Bool.or_true]

/-- The aggregated conversion (PROTOCOL.md#the-complete-protocol). -/
theorem hasSlashableWeightBetween_of_hasE2WeightAt {E : Env V} {h : Height}
    {T₁ T₂ : BlockId} {A₁ A₂ : Finset (CombinedAttestation V)} (hne : T₁ ≠ T₂)
    (hev : HasE2WeightAt E h T₁ T₂ A₁ A₂) : HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hE⟩ := hev
  exact ⟨S, hw, fun i hi => slashableBetween_of_e2EvidenceAtHeight hne (hE i hi)⟩

/-- **Lemma U** (rev. 3 §1.3; PROTOCOL.md#the-complete-protocol): two target quorums at one
height for **different** roots expose `2q − W` of E2 weight, at that height,
against those two roots.

Hence *"absent `2q − W` of E2-slashable weight, at most one target is justified
at any height, on any chain, anywhere in the run"* — and hence the lex tiebreak
on `(h_j, J.root)` never arbitrates between two real certificates
(`Finality.lean:52–70`, rev. 3 §1.3): the root component separates only events
at the same height, and by this lemma two real justifications never share one.

Nothing about chains, stores or reachability enters. The quorums are abstract
sets with per-member witnesses drawn one from each attestation pool, which is the
same evidence discipline `SlashableBetween` uses — the pool a witness comes
from is named, never existentially closed. -/
theorem justification_unique_per_height (E : Env V)
    {A₁ A₂ : Finset (CombinedAttestation V)} {Q₁ Q₂ : Finset V} {h : Height}
    {T₁ T₂ : BlockId}
    (hQ₁ : E.electorate.IsQuorum Q₁) (hQ₂ : E.electorate.IsQuorum Q₂)
    (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.val_index = i ∧ a.height_pair = .target h T₁)
    (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.val_index = i ∧ b.height_pair = .target h T₂) :
    HasE2WeightAt E h T₁ T₂ A₁ A₂ := by
  refine ⟨Q₁ ∩ Q₂, quorum_intersection E hQ₁ hQ₂, ?_⟩
  intro i hi
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_inter.mp hi
  obtain ⟨a, ha, hav, hpa⟩ := hw₁ i hi₁
  obtain ⟨b, hb, hbv, hpb⟩ := hw₂ i hi₂
  exact ⟨a, ha, b, hb, hav, hbv, hpa, hpb⟩

/-- **Lemma U**, in `Props`' own evidence vocabulary (PROTOCOL.md#the-complete-protocol):
two conflicting justifications at one height are `2q − W` of slashable weight
between the two pools. This is the form P5's lex-tiebreak argument (rev. 3 §1.3,
scenario S4) cites. -/
theorem justification_unique_per_height_slashable (E : Env V)
    {A₁ A₂ : Finset (CombinedAttestation V)} {Q₁ Q₂ : Finset V} {h : Height}
    {T₁ T₂ : BlockId} (hne : T₁ ≠ T₂)
    (hQ₁ : E.electorate.IsQuorum Q₁) (hQ₂ : E.electorate.IsQuorum Q₂)
    (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.val_index = i ∧ a.height_pair = .target h T₁)
    (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.val_index = i ∧ b.height_pair = .target h T₂) :
    HasSlashableWeightBetween E A₁ A₂ :=
  hasSlashableWeightBetween_of_hasE2WeightAt hne
    (justification_unique_per_height E hQ₁ hQ₂ hw₁ hw₂)

end Engine
end Proofs
end DecoupledConsensusModel

end
