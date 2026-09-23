module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Engine
public import DecoupledConsensusProofs.Protocol.ChainState.Certificates
public import DecoupledConsensusInternal.Optimistic

@[expose] public section

/-!
# The aligned-round derived lemmas L1–L4
(**rev. 4** §4; PROTOCOL.md#the-complete-protocol,
644–667, 755–775, 820–862, 1122–1200)

Rev. 4 deletes two clauses from `Internal.AlignedRound` — (c) a common
justification, and (e) no honest double vote — and adds (f) `Σ.h_max > h*`. This
file is what pays for the deletion. Four lemmas, in dependency order:

* **L4 `honest_no_double_target`** — (e), proved. A validator's attestation
  emissions in a run carry at most one nonempty target per height, in either
  pair, and no two of them are slashable. **Unconditional**: no admissibility,
  no fault bound, not even honesty. The run-level Λ-history bridge rev. 3 said
  was missing is `recordOk` below, and it is one induction over the event list.
* **L2 `no_off_can_finalization`** — (c)'s last defence, discharged. A finality
  certificate at a height `Can`'s own chain has crossed cannot conflict with
  `Can`. This is the quorum clash: `Can` carries a crossing quorum at that
  height, the two quorums intersect in `2q − W`, and every member of the
  intersection signed a height pair and a finality pair at one height with
  different targets, which is E1. It needs **only the accountable bound**
  `SlashableBound` — no P2, no honesty, no bound on the adversary's size, since
  the intersection members *are* the slashable weight. Same for
  `target_unique_of_slashableBound`, which is Lemma U's consumer form and
  scenario S4's answer.
* **L3 `sub_frontier_reveal_harmless`** — the certificate *below* `h*` that
  rev. 3 kept clause (c)'s lex floor for. Clause (f) makes the cascade gate
  unsatisfiable for it, so `get_fg_root` never selects it. It carries **no
  fault bound at all**, which is a fortiori the accountable one.
* **L1 `gate_selects_canonical`** — the conclusion (C3) consumes: every honest
  fork-choice root is an **ancestor** of `Can`. The gate-fires case runs on (f)
  and (d′), the gate-fails case on L2. Both of those give *compatibility* only,
  and the `Can ⪯ root` horn they leave open is inhabited: justification runs on
  a target quorum at the gate while confirmation is a separate walk, so a
  justified block can be strictly deeper than the deepest honest
  `live_confirmed`. The step from compatibility to `⪯` is therefore a depth
  bound, carried as `RootProvenance.{just_depth, fin_depth}` (amended per rev. 4
  review, finding 2).

## The two fault bounds, per site

Rev. 4 names two and pays the stronger price only where it must
(`Execution.{SlashableBound, BelowOneThird}`).

* **`SlashableBound`** — L2 and Lemma U (scenario S4). The conflicting objects
  convict their own signers: the quorum intersection *is* the slashable weight,
  so no honesty argument and no count of faulty weight enters.
* **`BelowOneThird`** — L1's gate-fires case, and every Lemma G4 use: the
  (d′)-preservation half of P4's induction, P4-L, and P5. A quorum contains
  honest weight only when the adversary cannot form one alone.
* **neither** — P1 and L3. P1 *produces* the evidence and consumes no bound; L3
  closes the cascade gate by arithmetic on clause (f) and counts no weight at
  all (amended per rev. 4 review, finding 7).

The gap is not slack. **Fresh adversarial votes at a height nobody has voted at
are not slashable against anything**, so with `b ≥ q` the adversary assembles an
off-`Can` certificate and leaves no evidence: the accountable bound cannot
exclude it, and anything that must carries `BelowOneThird`. The bridge runs one
way — `slashableBound_of_belowOneThird` — and it spends L4 plus the
carried-attestation premise.

The implication reading of P1 — "no `2q − W` slashable between two histories ⟹
their finalizations are compatible" — is `Internal.ChainAccountableSafety` composed
with `SlashableBound`, and **L2 is its consumer**. It is deliberately not a
declaration of its own: the disjunctive headline stays the only public P1
statement, because it is the form that hands the caller the names, and a named
implication would add review surface with no consumer L2 does not already serve.

## What is proved outright and what is hypothesized

Three bridges are named rather than proved, and each is named for a reason the
statement surface already records.

* `CarriedByHonest` — an attestation a *block* carries in an honest validator's
  name is that validator's own emission. `Admissible.carried_attest` says exactly
  this, but only for a block some node has **processed**; nothing at this layer
  says every ancestor of `Can` was processed, and P1's own store corollary is
  blocked on the same gap (design note P1). Carried as a hypothesis.
* `Execution.RootInjectiveOnAncestors` — P1's standing scoped premise. The transition
  compares **roots** while the conclusions are about blocks
  (modeling-choices rows 12, 4.1), so it is unavoidable here for the same reason
  it is unavoidable in `Protocol.Main`.
* `RootProvenance` — L1's bundle. Its two certificate fields say an honest
  store's `(J, h_j)` and `F` were written by `update_finality` from the state of
  a block the store holds, and its `crossed` field is rev. 3 §4.4's ladder fact.
  Both are P6 / (C3) obligations about reachable stores, not facts about the
  predicate, and together they are the only thing standing between L1 and being
  unconditional under the predicate.

L4 is the one that was supposed to be hard, and it is not: it needs none of the
three.

`justification_certificate` below is **not** hypothesized: it is the target-quorum
mirror of `Protocol.finality_certificate`, proved here by the same structural
induction, because L1's gate-fires case needs it and the P1 track never had a
reason to extract it.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace AlignedRoundLemmas

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. The fault bound and its consequence (PROTOCOL.md#the-complete-protocol) -/

/-- §4 `2W ≤ 3q`: the quorum threshold really is two thirds
(PROTOCOL.md#the-complete-protocol). Everything below reflects through this and then runs on
`omega`, exactly as `Electorate.isQuorum_iff_three_mul_weight` does. -/
theorem two_mul_W_le_three_mul_q (E : Env V) : 2 * E.W ≤ 3 * E.q := by
  unfold Env.q Env.W Electorate.finalityThreshold
  omega

/-- **`BelowOneThird` implies `HonestQuorum`** (rev. 4 §4; PROTOCOL.md#the-complete-protocol,
532–535).

`w(H) + w(V \ H) = W` and `3 · w(V \ H) < W` give `3 · w(H) > 2W ≥ 3q − 2`, and
the ceiling arithmetic closes the gap in each residue class of `W` mod 3. -/
theorem honestQuorum_of_belowOneThird {S : Setup V} {H : Finset V}
    (h : BelowOneThird S H) : HonestQuorum S H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold BelowOneThird at h
  unfold HonestQuorum
  unfold Env.q Env.W Electorate.finalityThreshold at *
  omega

/-- The healing fault bound implies the weaker honest-weight majority used by
the available-chain layer. This is composition glue: a post-healing
confirmation theorem can state only its own one-half premise, while an
end-to-end theorem that already assumes the stronger healing bound can
discharge that premise here. -/
theorem honestWeightMajority_of_belowOneThird
    {S : Setup V} {H : Finset V}
    (h : BelowOneThird S H) : HonestWeightMajority S H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold BelowOneThird at h
  unfold HonestWeightMajority
  unfold Env.W at h
  omega

/-- The faulty weight, as the complement of the honest set. Named so the
quorum-clash arithmetic reads the way rev. 4 §4 writes it. -/
theorem weight_le_faulty_of_subset {S : Setup V} {H X : Finset V}
    (hX : ∀ i ∈ X, i ∉ H) :
    S.E.electorate.weightOf X ≤ S.E.electorate.weightOf (Finset.univ \ H) :=
  S.E.electorate.weightOf_mono (fun i hi =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hX i hi⟩)

/-- **The quorum clash, as arithmetic** (rev. 4 §4; PROTOCOL.md#the-complete-protocol). An
intersection of two quorums carries `2q − W`, and under the fault bound no such
weight fits inside the faulty set. This is the whole of why deleted clause (c)'s
last defence — a late conflicting finalization — is not merely excluded by
hypothesis but **impossible**. -/
theorem no_faulty_intersection {S : Setup V} {H X : Finset V}
    (hbot : BelowOneThird S H) (hw : HasIntersectionWeight S.E X)
    (hX : ∀ i ∈ X, i ∉ H) : False := by
  have hle := weight_le_faulty_of_subset (S := S) hX
  have hq := two_mul_W_le_three_mul_q S.E
  unfold BelowOneThird at hbot
  unfold HasIntersectionWeight at hw
  omega



/-! ## 3. The run-level Λ-history bridge (design §2.3; PROTOCOL.md#the-complete-protocol)

Rev. 3 stated clause (e) because this bridge did not exist. It is one induction
over the event list, and it needs nothing from `Admissible`: a validator's record
is written by its **own** ticks alone, because `World.step` writes through
`Function.update` and `NodeState.process` never touches `Λ`. -/



/-! ## 5. L2 — no off-`Can` finalization at a crossed height
(PROTOCOL.md#the-complete-protocol)

This is the argument that lets deleted clause (c) go. Rev. 3 kept (c) so that a
*late-revealed* conflicting finalization could not move `Σ.J` and then `Σ.F`.
Under the fault bound the object it defends against does not exist. -/

/-- Every attestation of `A` attributed to a member of `H` is that validator's
own emission somewhere in the run.

This is `Execution.Unforgeable.carried_attest`, scoped to a pool. It is a
hypothesis rather than a consequence because that clause is stated over a block
some node has **processed**, and nothing at this layer says every ancestor of
`Can` was processed anywhere; P1's own store corollary is blocked on the same
gap (design note P1).

The run emits named rows, while the pool `A` is the erased accountability view,
so the witness is the named row that erases to `a`. -/
def CarriedByHonest (S : Setup V) (ρ : Run V) (H : Finset V)
    (A : Finset (CombinedAttestation V)) : Prop :=
  ∀ a ∈ A, a.val_index ∈ H →
    ∃ (row : NamedAttestation V) (t : Time),
      row.erase = a ∧ ρ.emits S a.val_index (Object.attest row) t





/-- Under the fault bound every quorum meets the honest set. The degenerate
`W = 0` electorate is excluded by `BelowOneThird` itself: `3 · w(faulty) < W`
forces `0 < W`. -/
theorem honest_member_of_quorum {S : Setup V} {H Q : Finset V}
    (hbot : BelowOneThird S H) (hQ : S.E.electorate.IsQuorum Q) :
    ∃ i ∈ Q, i ∈ H := by
  by_contra hno
  -- `push Not`, not `push_neg`: the latter is deprecated in this toolchain
  -- (rev. 4 review, finding 12, checked against Lean 4.30-rc2 and reversed).
  push Not at hno
  exact no_faulty_intersection hbot
    (honest_part_of_quorum S.E hQ (honestQuorum_of_belowOneThird hbot))
    (fun i hi => hno i (Finset.mem_inter.mp hi).1)



-- compatibility/Proofs/AlignedRoundLemmasRetired.lean.



/-! ### The bridge: the adversarial bound implies the accountable one -/


/-- **`BelowOneThird` + the run's honesty ⟹ no slashable weight between two
pools** (rev. 4 §13.2; PROTOCOL.md#the-complete-protocol).

One half is proved here: a faulty set of weight `2q − W` contradicts
`3 · w(faulty) < W`. The other half — an honest validator never produces
slashable evidence — was `Proofs.SelfSafety.honest_no_pair_slashing`, and it
retired with the record layer the baseline replaced
(`the design notes`).

It is therefore a **named FOR-REVIEW conditional** now, `NoSelfSlashing`, rather
than a theorem. It is not a new assumption about the world: it is a fact about
the record discipline, it was proved before, and it will be proved again against
`record_attestation`. Carrying it explicitly is what keeps the retirement
visible at every consumer instead of hidden in an import.

`CarriedByHonest` is the third ingredient and it is the same named bridge L1
carries: what a *block* holds in an honest validator's name has to be that
validator's own emission before P2 can be applied to it. -/
def NoSelfSlashing (S : Setup V) (ρ : Run V) : Prop :=
  ∀ (i : V) (a b : NamedAttestation V),
    (∃ t : Time, ρ.emits S i (Object.attest a) t) →
    (∃ t : Time, ρ.emits S i (Object.attest b) t) →
    Protocol.slashable a.erase b.erase = false

theorem noSlashableWeightBetween_of_belowOneThird {S : Setup V} {ρ : Run V}
    {H : Finset V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (hbot : BelowOneThird S H) (hself : NoSelfSlashing S ρ)
    (h₁ : CarriedByHonest S ρ H A₁) (h₂ : CarriedByHonest S ρ H A₂) :
    ¬ HasSlashableWeightBetween S.E A₁ A₂ := by
  rintro ⟨X, hw, hX⟩
  refine no_faulty_intersection hbot hw ?_
  intro i hi hiH
  obtain ⟨a, ha, b, hb, hav, hbv, hsl⟩ := hX i hi
  obtain ⟨ra, ta, hra, hea⟩ := h₁ a ha (by rw [hav]; exact hiH)
  obtain ⟨rb, tb, hrb, heb⟩ := h₂ b hb (by rw [hbv]; exact hiH)
  have hsafe := hself i ra rb ⟨ta, hav ▸ hea⟩ ⟨tb, hbv ▸ heb⟩
  rw [hra, hrb] at hsafe
  have hsl' : Protocol.slashable a b = true := hsl
  rw [hsafe] at hsl'
  simp at hsl'

/-- **The run-level bridge** (rev. 4 §13.2): the adversarial bound and the run's
honesty give the accountable bound. `HonestQuorum` comes from the same place
(`honestQuorum_of_belowOneThird`), so a statement carrying `BelowOneThird` and
the carried-attestation bridge carries everything below it. -/
theorem slashableBound_of_belowOneThird {S : Setup V} {ρ : Run V}
    (hbot : BelowOneThird S ρ.honest) (hself : NoSelfSlashing S ρ)
    (hcar : ∀ B : NamedBlock V, RunBlock S ρ B →
      CarriedByHonest S ρ ρ.honest (chain_attestations B.erase)) :
    SlashableBound S ρ :=
  fun _ _ hB₁ hB₂ =>
    noSlashableWeightBetween_of_belowOneThird hbot hself (hcar _ hB₁) (hcar _ hB₂)

/-! ## 6. L3 — a sub-`h*` reveal is inert (PROTOCOL.md#the-complete-protocol)

Rev. 3 kept clause (c)'s lex floor for exactly one attack: a certificate at a
height **below** `h*` whose root sorts higher, revealed late to steal `Σ.J` and
with it the fork-choice root. Clause (f) closes it at the gate instead, and the
`F`-guard has nothing to accept by L2. -/


/-! ## 7. L1 — the gate selects a canonical root (PROTOCOL.md#the-complete-protocol) -/



/-! ## 7. L1 — the gate selects a canonical root (PROTOCOL.md#the-complete-protocol) -/

/-- §4 a chain state's height never drops below one (PROTOCOL.md#the-complete-protocol,
660–662): `ChainState.initial.h = 1` and `advance_height` only increments. -/
theorem one_le_derived_h (E : Env V) (cfg : HeightConfig) :
    ∀ B : Block V, 1 ≤ (derived_state E cfg B).h := by
  intro B
  induction B with
  | genesis => exact Nat.le_refl 1
  | node p s r gv gsv ats i ih =>
      rw [Protocol.derived_state_node, Protocol.process_height_events_eq]
      split_ifs
      · rw [Protocol.advance_height_h]; exact Nat.le_add_left 1 _
      · rw [Protocol.advance_height_h]; exact Nat.le_add_left 1 _
      · rw [Protocol.afterFin_h, Protocol.foldBlock_h]; exact ih

/-- §4 `h_j = 0` means the chain never justified, so `J` is genesis
(PROTOCOL.md#the-complete-protocol). -/
theorem derived_state_J_of_h_j_zero (E : Env V) (cfg : HeightConfig) :
    ∀ B : Block V, (derived_state E cfg B).h_j = 0 →
      (derived_state E cfg B).J = Block.genesis := by
  intro B
  induction B with
  | genesis => intro _; rfl
  | node p s r gv gsv ats i ih =>
      intro h
      rw [Protocol.derived_state_node] at h ⊢
      rw [Protocol.process_height_events_eq] at h ⊢
      split_ifs at h ⊢ with h1 h2
      · exfalso
        have hh : (Protocol.afterFin E (Protocol.foldBlock (derived_state E cfg p)
            (Block.node p s r gv gsv ats i))).h = 0 := h
        rw [Protocol.afterFin_h, Protocol.foldBlock_h] at hh
        have h1 := one_le_derived_h E cfg p
        rw [hh] at h1
        simp at h1
      · rw [Protocol.advance_height_J, Protocol.afterFin_J, Protocol.foldBlock_J]
        rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, Protocol.foldBlock_h_j] at h
        exact ih h
      · rw [Protocol.afterFin_J, Protocol.foldBlock_J]
        rw [Protocol.afterFin_h_j, Protocol.foldBlock_h_j] at h
        exact ih h

omit [Fintype V] in
/-- **Compatibility plus a depth bound is ancestry** (PROTOCOL.md#the-complete-protocol).

The step L1 needs to reach `⪯` from what (d′) and L2 give. `compatible B C` is
`B ⪯ C ∨ C ⪯ B`, and the second horn puts `C` no deeper than `B`
(`Block.preceq_depth_le`), so `B.depth ≤ C.depth` collapses it to `B = C`
(`Block.preceq_eq_of_depth_le`).

**Depth, not chain-state height.** `(derived_state ·).h` will not do here: it is
monotone but not strictly so along a chain, so a block strictly below `C` can
report the same height and the collapse fails. Depth is the measure the ancestry
kit is built on, and it is the one that separates the two horns. -/
theorem preceq_of_compatible_of_depth_le {B C : Block V}
    (hcmp : Block.compatible B C = true) (hd : B.depth ≤ C.depth) :
    Block.Preceq B C := by
  simp only [Block.compatible, Bool.or_eq_true] at hcmp
  rcases hcmp with h | h
  · exact h
  · have hCB : C = B := Block.preceq_eq_of_depth_le h hd
    subst hCB
    exact Block.preceq_self _






end AlignedRoundLemmas
end Proofs
end DecoupledConsensusModel

end
