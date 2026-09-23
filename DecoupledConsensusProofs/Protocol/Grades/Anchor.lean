module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
public import DecoupledConsensusProofs.Protocol.Grades.LegacyVocabulary

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The cone test (PROTOCOL.md#the-complete-protocol)

`Protocol.heads_under` and `Protocol.head_covers` are the same test written
twice — one takes a vote, the other its head field — so one predicate serves the
grades and the relative majority alike. -/

/-- A head root lies in `Can`'s cone: resolved in `T`, it is an ancestor of
`Can`. The empty head and an unresolvable root both qualify, because neither
supports anything (PROTOCOL.md#the-complete-protocol, modeling-choices row 1). -/
def rootOnCan (T : Finset (Block V)) (Can : Block V) : Option BlockId → Bool
  | none => true
  | some root =>
    match Block.find? T root with
    | some H => Block.preceq H Can
    | none => true

omit [DecidableEq V] [Fintype V] in
/-- §6.2 the head tie-break is irreflexive (PROTOCOL.md#the-complete-protocol). -/
theorem head_lt_irrefl (h : Option BlockId) : Protocol.head_lt h h = false := by
  cases h <;> simp [Protocol.head_lt]

omit [DecidableEq V] [Fintype V] in

/-- §6.2 the batch order is irreflexive, so a lone vote is its own first
(PROTOCOL.md#the-complete-protocol). -/
theorem batch_before_irrefl (ts : TimestampMap (SGVote V)) (u : SGVote V) :
    Protocol.batch_before ts u u = false := by
  unfold Protocol.batch_before
  cases hx : ts u with
  | none => simpa using head_lt_irrefl u.confirmed
  | some y => simp [head_lt_irrefl]


/-- **The honest round batch, seen from one store** (rev. 4 §4.2 clauses (a),
(b); PROTOCOL.md#the-complete-protocol).

Both clauses are about the *reader's* pool: the honest validators' round-`(r−1)`
votes as this store holds them. `sole` is honesty plus `Unforgeable.unforgeable` —
nothing speaks for an honest validator, and an honest validator speaks once per
round — and `heads` is clause (b)'s head alignment. -/
structure BatchAligned (gv : GradeView V) (Hon : Finset V) (r : Round)
    (Can : Block V) : Prop where
  
  sole : ∀ v ∈ Hon, (Protocol.sg_votes_by (Protocol.round_batch gv r) v).card ≤ 1
  
  heads : ∀ v ∈ Hon, ∀ u ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) v,
    rootOnCan gv.T Can u.confirmed = true
theorem summary_C_v_mem (gv : GradeView V) (r : Round) (v : V) :
    (Protocol.summary gv r v).C_v = none ∨
      ∃ u ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) v,
        (Protocol.summary gv r v).C_v = u.confirmed := by
  set named := (Protocol.sg_votes_by (Protocol.round_batch gv r) v).filter
    (fun u => u.confirmed.isSome ∧
      Protocol.sg_resolved gv.T u = true) with hnamed
  set τ := Protocol.sg_resolution_time gv.T gv.timestamp_block
    gv.timestamp_sg_vote with hτ
  have hHv : (Protocol.summary gv r v).C_v =
      (Protocol.batch_first? τ named).bind SGVote.confirmed := rfl
  cases hh : Protocol.batch_first? τ named with
  | none => exact Or.inl (by rw [hHv, hh]; rfl)
  | some w =>
    have hmem : w ∈ named := by
      unfold Protocol.batch_first? at hh
      exact Proofs.Engine.pickUnique?_mem hh
    exact Or.inr ⟨w, Finset.mem_of_mem_filter w hmem, by rw [hHv, hh]; rfl⟩
theorem summary_C_v_onCan {gv : GradeView V} {Hon : Finset V} {r : Round}
    {Can : Block V} (hal : BatchAligned gv Hon r Can) {v : V} (hv : v ∈ Hon) :
    rootOnCan gv.T Can (Protocol.summary gv r v).C_v = true := by
  rcases summary_C_v_mem gv r v with h | ⟨u, hu, h⟩
  · rw [h]; rfl
  · rw [h]; exact hal.heads v hv u hu

omit [Fintype V] in
/-- §6.2 the first vote of a set with at most one member is that member
(PROTOCOL.md#the-complete-protocol). -/
theorem batch_first?_of_card_le_one {ts : TimestampMap (SGVote V)}
    {S : Finset (SGVote V)} {u : SGVote V} (hu : u ∈ S) (hcard : S.card ≤ 1) :
    Protocol.batch_first? ts S = some u := by
  have huniq := Finset.card_le_one.mp hcard
  refine Protocol.pickUnique?_eq_some hu ?_ (fun a ha _ => huniq a ha u hu)
  simp only [Protocol.is_first_in, decide_eq_true_eq]
  intro w hw
  rw [huniq w hw u hu]
  exact batch_before_irrefl ts u


omit [Fintype V] in
/-- §3.3 the vote form and the §6.2 head form are one test
(PROTOCOL.md#the-complete-protocol). -/
theorem heads_under_eq_head_covers (T : Finset (Block V)) (B : Block V)
    (vote : SGVote V) :
    Protocol.heads_under T B vote = Protocol.head_covers T B vote.confirmed :=
  rfl

omit [Fintype V] in
/-- **The cone step.** A block covered by a head in `Can`'s cone is itself in
`Can`'s cone (PROTOCOL.md#the-complete-protocol). -/
theorem preceq_of_head_covers {T : Finset (Block V)} {Can B : Block V}
    {H : Option BlockId} (hcov : Protocol.head_covers T B H = true)
    (hon : rootOnCan T Can H = true) : Block.preceq B Can = true := by
  cases H with
  | none => exact absurd hcov (by simp [Protocol.head_covers])
  | some root =>
    simp only [Protocol.head_covers] at hcov
    simp only [rootOnCan] at hon
    cases hf : Block.find? T root with
    | none => rw [hf] at hcov; exact absurd hcov (by simp)
    | some head =>
      rw [hf] at hcov hon
      exact Block.preceq_trans hcov hon





omit [Fintype V] in

/-- §6.2 a batch slice with at most one vote has no equivocation instant
(PROTOCOL.md#the-complete-protocol).

Stated over the batch and the receipt clock alone, with **no tree**: that is the
τ fold's split made usable, and it is why the two callers of this fact — here and
`Proofs.HealingLemmas.Grades` — share one lemma instead of routing through a
`GradeView` with a doctored tree. -/
theorem equivocation_instant_eq_none {ts : TimestampMap (SGVote V)}
    {batch : Finset (SGVote V)} (hcard : batch.card ≤ 1) :
    Protocol.equivocation_instant ts batch = none := by
  unfold Protocol.equivocation_instant
  cases hf : Protocol.batch_first? ts batch with
  | none => rfl
  | some first =>
    have hfmem : first ∈ batch := by
      unfold Protocol.batch_first? at hf
      exact Proofs.Engine.pickUnique?_mem hf
    have hempty : batch.filter (fun u => u.confirmed ≠ first.confirmed) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro u hu
      simp only [not_not]
      rw [Finset.card_le_one.mp hcard u hu first hfmem]
    simp only [hempty, Protocol.batch_first?, pickUnique?]
    rw [dif_neg (by rintro ⟨a, ⟨ha, -⟩, -⟩; exact absurd ha (by simp))]

omit [Fintype V] in
/-- §6.2 `e_v` is `equivocation_instant` at `v`'s slice (PROTOCOL.md#the-complete-protocol).
Written down because unifying through `summary`'s `let`s is expensive. -/
theorem summary_e_v_eq (gv : GradeView V) (r : Round) (v : V) :
    (Protocol.summary gv r v).e_v =
      Protocol.equivocation_instant gv.timestamp_sg_vote
        (Protocol.sg_votes_by (Protocol.round_batch gv r) v) := rfl


/-- Weight carried by a set none of whose members is honest is faulty weight
(PROTOCOL.md#the-complete-protocol). -/
theorem weight_filter_le_faulty (E : Env V) {Hon : Finset V} {p : V → Prop}
    [DecidablePred p] (h : ∀ v, p v → v ∉ Hon) :
    E.electorate.weightOf (Finset.univ.filter p) ≤
      E.electorate.weightOf (Finset.univ \ Hon) :=
  E.electorate.weightOf_mono (fun i hi =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h i (Finset.mem_filter.mp hi).2⟩)



/-- **The honest SG batch, seen from one store** (rev. 4 §4.2 clauses (a),
(b)).

`represented` is clause (a): every honest validator emitted its round-`(r−1)`
attestation and every honest store holds it, so every honest validator has a
latest round. `heads` is clause (b): the vote `supports` actually reads has its
head in `Can`'s cone. -/
structure SupportAligned (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (Hon : Finset V) (r : Round) (Can : Block V) : Prop where
  /-- Every honest validator counts in the denominator. Raw since baseline
  `c9c98df` — representation reads receipt, not resolution, so this clause got
  strictly **weaker** (a held vote suffices, resolved or not). -/
  represented : ∀ v ∈ Hon, Protocol.represented pool η_SG v r = true
  /-- The vote the support rule reads has its head in `Can`'s cone — stated at
  the selector `latest_support_vote` (baseline `c9c98df`). -/
  heads : ∀ v ∈ Hon, ∀ u : SGVote V,
    Protocol.latest_support_vote pool η_SG T v r = some u →
      rootOnCan T Can u.confirmed = true

omit [Fintype V] in
/-- §3.3 an honest validator supports nothing off `Can`'s chain
(PROTOCOL.md#the-complete-protocol). -/
theorem not_supports_off_can {pool : Round → Finset (SGVote V)} {η_SG : Round}
    {T : Finset (Block V)} {Hon : Finset V} {r : Round} {Can B : Block V}
    (hal : SupportAligned pool η_SG T Hon r Can) {v : V} (hv : v ∈ Hon)
    (hB : Block.preceq B Can = false) :
    Protocol.supports pool η_SG T r B v = false := by
  rw [← Bool.not_eq_true]
  intro hsup
  simp only [Protocol.supports] at hsup
  split at hsup
  · exact absurd hsup (by simp)
  · rename_i u hu
    rw [heads_under_eq_head_covers] at hsup
    exact absurd (preceq_of_head_covers hsup (hal.heads v hv u hu))
      (by rw [hB]; simp)

/-- §3.3 a block off `Can`'s chain is supported by faulty weight alone
(PROTOCOL.md#the-complete-protocol). -/
theorem sg_support_le_faulty (E : Env V) {pool : Round → Finset (SGVote V)}
    {η_SG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {Can B : Block V} (hal : SupportAligned pool η_SG T Hon r Can)
    (hB : Block.preceq B Can = false) :
    Protocol.sg_support E pool η_SG T r B ≤
      E.electorate.weightOf (Finset.univ \ Hon) := by
  simp only [Protocol.sg_support, Protocol.sgSupporters]
  refine weight_filter_le_faulty E ?_
  intro v hsup hvH
  rw [not_supports_off_can hal hvH hB] at hsup
  exact absurd hsup (by simp)






/-- §6.2 a block off `Can`'s chain draws **direct** support from faulty weight
alone (PROTOCOL.md#the-complete-protocol). Needs only the head half of `BatchAligned`. -/
theorem direct_support_le_faulty (E : Env V) {gv : GradeView V} {Hon : Finset V}
    {r : Round} {Can B : Block V} {Γ_h Γ_e : Time}
    (hal : BatchAligned gv Hon r Can) (hB : Block.preceq B Can = false) :
    Protocol.direct_support E gv r Γ_h Γ_e B ≤
      E.electorate.weightOf (Finset.univ \ Hon) := by
  simp only [Protocol.direct_support]
  refine weight_filter_le_faulty E ?_
  intro v hp hvH
  obtain ⟨-, hcov, -⟩ := hp
  exact absurd (preceq_of_head_covers hcov (summary_C_v_onCan hal hvH))
    (by rw [hB]; simp)

/-! ## 4. The two consequences (C3) and P4-L name -/




end Optimistic
end Proofs
end DecoupledConsensusModel

end
