module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section

/-!
# P3(a) — the confirmation count
(§2.6 `alg:confirmation`, PROTOCOL.md#the-complete-protocol; §7.2's re-anchored version,
PROTOCOL.md#the-complete-protocol)

"Confirmation is the same walk over a stricter vote set and a larger
denominator" (PROTOCOL.md#the-complete-protocol). This module is what that sentence buys.

**The stricter vote set has no equivocators.** `early ⊆ late` is a stated
property of the two cutoffs (PROTOCOL.md#the-complete-protocol) and `no_second_vote_in late`
is tested against the *larger* set, so a validator with two votes anywhere in
`late` contributes to `votes` not once but **zero** times. Hence `votes` holds at
most one vote per validator, `Protocol.equivocators` is empty on it, and
`goldfish_score` degenerates to the plain supporter count
(`score_eq_supporters`). Every counting argument below rests on that one fact,
and none of them needs honest committees.

Two consequences, and they are the two halves of P3(a).

* **Safety needs no majority at all.** Supporters of conflicting blocks are
  disjoint, so at one node two conflicting blocks cannot both clear the gate.
  Across two nodes the same argument runs on a *synchrony* interface —
  `CrossView`: every vote counted here either reaches the other late view, or
  that view already holds two votes by its validator — and gives
  `2(a + b) ≤ count_v + count_w < 2a + 2b`, a contradiction. This is
  `eligible_compatible`, and its hypotheses are counting and reachability only:
  no `HonestCommittees`, no `HonestQuorum`.
* **Liveness is where the majority enters.** `HonestSupport` says every honest
  committee member's slot-`s` vote resolves to `B`. Then every ancestor of `B`
  clears the gate and strictly outscores its siblings, and nothing strictly below
  `B` clears it — which is exactly `Walk.lean`'s `ghost_reaches` interface.

The `2·score > voters_count` arithmetic is the one place `HonestCommittees`'
`|K_s| < 2·|K_s ∩ H|` is consumed (PROTOCOL.md#the-complete-protocol).
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The two cutoffs (PROTOCOL.md#the-complete-protocol) -/

omit [DecidableEq V] [Fintype V] in
/-- §1 a wider cutoff sees more: `beforeCutoff` is monotone in `Γ`
(PROTOCOL.md#the-complete-protocol). This is the model's form of "the early set is contained in
the late set" (PROTOCOL.md#the-complete-protocol). -/
theorem beforeCutoff_mono {α : Type} [DecidableEq α] (ts : TimestampMap α)
    {Γ Γ' : Time} (h : Γ ≤ Γ') (S : Finset α) :
    beforeCutoff ts Γ S ⊆ beforeCutoff ts Γ' S := by
  intro x hx
  rw [beforeCutoff, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hs := hx.2
  unfold stampedBefore at hs ⊢
  cases hts : ts x with
  | none =>
      rw [hts] at hs
      exact absurd hs (by simp)
  | some u =>
      rw [hts] at hs
      simp only [decide_eq_true_eq] at hs ⊢
      exact lt_of_lt_of_le hs (WithBot.coe_le_coe.mpr h)

/-- §2.1 the support cutoff precedes the confirmation evaluation
(PROTOCOL.md#the-complete-protocol): `t_s + 2Δ ≤ t_s + 6Δ`, because `Δ > 0`. Together with
`beforeCutoff_mono` this is `early ⊆ late` (PROTOCOL.md#the-complete-protocol).

The arithmetic is routed through a plain `Int` statement: `omega` does not see
linear facts through the `Time`/`Slot` abbrevs at a projection like `E.t s`. -/
theorem support_cutoff_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.confirmation_time E s := by
  have key : ∀ a d : Int, 0 ≤ d → a + 2 * d ≤ a + 6 * d := by
    intro a d hd; omega
  exact key (E.t s) E.Δ (le_of_lt E.Δ_pos)

/-! ## The numerator has at most one vote per validator -/

/-- The shape of `update_confirmation`'s numerator (PROTOCOL.md#the-complete-protocol): the
early set, filtered by "the late set holds no second vote by this validator".

Stated abstractly over the two sets so that §2's version and §7's re-anchored
version (PROTOCOL.md#the-complete-protocol) are one instance each; the only thing the
lemmas below read is `early ⊆ late`, which is the stated property of the two
cutoffs. -/
structure Numerator (early late votes : Finset (GoldfishVote V)) : Prop where
  /-- PROTOCOL.md#the-complete-protocol, the model's `beforeCutoff_mono`. -/
  early_late : early ⊆ late
  /-- PROTOCOL.md#the-complete-protocol. -/
  filtered : votes = early.filter (fun u => Protocol.no_second_vote_in late u = true)

namespace Numerator

variable {early late votes : Finset (GoldfishVote V)}

omit [Fintype V] in
/-- The numerator is inside the early set. -/
theorem subset_early (h : Numerator early late votes) : votes ⊆ early := by
  rw [h.filtered]; exact Finset.filter_subset _ _

omit [Fintype V] in
/-- The numerator is inside the late set. -/
theorem subset_late (h : Numerator early late votes) : votes ⊆ late :=
  subset_trans h.subset_early h.early_late

omit [Fintype V] in
/-- **The one fact everything rests on.** A counted vote is its validator's only
vote in the *late* set, so any other vote of that validator anywhere in `late` is
the same vote (PROTOCOL.md#the-complete-protocol). -/
theorem unique_in_late (h : Numerator early late votes) {u u' : GoldfishVote V}
    (hu : u ∈ votes) (hu' : u' ∈ late) (hval : u'.val_index = u.val_index) : u' = u := by
  rw [h.filtered, Finset.mem_filter] at hu
  have := hu.2
  rw [Protocol.no_second_vote_in, decide_eq_true_eq] at this
  rcases this u' hu' with hEq | hNe
  · exact hEq
  · exact absurd hval hNe

omit [Fintype V] in
/-- A validator has at most one counted vote. -/
theorem votes_by_card_le_one (h : Numerator early late votes) (x : V) :
    (Protocol.votes_by votes x).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  rw [Protocol.votes_by, Finset.mem_filter] at ha hb
  exact h.unique_in_late hb.1 (h.subset_late ha.1) (by rw [ha.2, hb.2])

omit [Fintype V] in
/-- **No equivocators in the numerator** (PROTOCOL.md#the-complete-protocol). The filter is
tested against `late`, which already contains `early`, so a validator caught
equivocating by the late cutoff contributes nothing at all — it is not merely
"credited to every block" as in the fork choice (PROTOCOL.md#the-complete-protocol). -/
theorem no_equivocation (h : Numerator early late votes) (x : V) :
    Protocol.equivocates votes x = false := by
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  have := h.votes_by_card_le_one x
  omega

omit [Fintype V] in
/-- A validator whose vote survives the numerator filter is not an equivocator
in the wider late set. This is stronger than `no_equivocation`: the filter is
tested against `late`, not only against the numerator itself. -/
theorem no_equivocation_in_late (h : Numerator early late votes)
    {u : GoldfishVote V} (hu : u ∈ votes) :
    Protocol.equivocates late u.val_index = false := by
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  intro htwo
  have hle : (Protocol.votes_by late u.val_index).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [Protocol.votes_by, Finset.mem_filter] at ha hb
    have hau : a = u := h.unique_in_late hu ha.1 ha.2
    have hbu : b = u := h.unique_in_late hu hb.1 hb.2
    exact hau.trans hbu.symm
  omega

/-- §2.4 with no equivocators the **self-pair** score is the plain supporter
count (PROTOCOL.md#the-complete-protocol): `update_confirmation` passes
`(support_votes, support_votes)`, so both walk arguments are the numerator. -/
theorem score_eq_supporters (h : Numerator early late votes) (E : Env V)
    (T : Finset (Block V)) (s : Slot) (B : Block V) :
    Protocol.goldfish_score E T votes votes s B =
      (Protocol.goldfishSupporters E T votes votes s B).card := by
  rw [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  have hempty : Protocol.raw_equivocators votes = ∅ := by
    rw [Protocol.raw_equivocators, Finset.filter_eq_empty_iff]
    intro x _
    rw [h.no_equivocation x]
    simp
  rw [hempty, Finset.card_empty, Nat.zero_add, Protocol.goldfishSupporters]

end Numerator

/-! ## Supporters -/

omit [Fintype V] in
/-- §2.4 the supporter test, unfolded (PROTOCOL.md#the-complete-protocol). -/
theorem targets_under_iff {T : Finset (Block V)} {B : Block V} {u : GoldfishVote V} :
    Protocol.targets_under T B u = true ↔
      ∃ B', Block.find? T u.head = some B' ∧ B'.slot ≤ u.slot ∧
        Block.preceq B B' = true := by
  unfold Protocol.targets_under
  cases hfind : Block.find? T u.head with
  | none => simp
  | some B' => simp

/-- §2.4 membership in `supporters`, unfolded, at the two-view signature
(baseline `7b2efec`): the equivocation test reads `votes`, the vote itself comes
from `support_votes`. -/
theorem mem_supporters_iff {E : Env V} {T : Finset (Block V)}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} {x : V} :
    x ∈ Protocol.goldfishSupporters E T votes support_votes s B ↔
      Protocol.equivocates votes x = false ∧
      ∃ u ∈ Protocol.votes_by support_votes x, u.slot = s ∧
        Protocol.targets_under T B u = true := by
  simp only [Protocol.goldfishSupporters, Protocol.raw_supporters, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- §2.4 support is inherited by ancestors: if a vote's target descends from `B`
it descends from every ancestor of `B` (PROTOCOL.md#the-complete-protocol). -/
theorem supporters_mono (E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) {C B : Block V}
    (h : Block.preceq C B = true) :
    Protocol.goldfishSupporters E T votes support_votes s B ⊆
      Protocol.goldfishSupporters E T votes support_votes s C := by
  intro x hx
  rw [mem_supporters_iff] at hx ⊢
  obtain ⟨hne, u, hu, hslot, htar⟩ := hx
  obtain ⟨B', hfind, hpre⟩ := targets_under_iff.mp htar
  exact ⟨hne, u, hu, hslot, targets_under_iff.mpr
    ⟨B', hfind, hpre.1, Block.preceq_trans h hpre.2⟩⟩

/-- §2.4 a supporter has a counted **support** vote, so its validator
participates in any set that holds the support set
(PROTOCOL.md#the-complete-protocol). -/
theorem supporters_subset_participants (E : Env V) (T : Finset (Block V))
    {votes support_votes late' : Finset (GoldfishVote V)}
    (hsub : support_votes ⊆ late') (s : Slot) (B : Block V) :
    Protocol.goldfishSupporters E T votes support_votes s B ⊆
      Protocol.participants E late' s := by
  intro x hx
  rw [mem_supporters_iff] at hx
  obtain ⟨-, u, hu, -, -⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hsub hu.1, hu.2⟩

/-- §2.4 the participants of an ingress-valid slot view are members of its
committee (PROTOCOL.md#the-complete-protocol). Raw counting itself does not repeat this
filter. -/
theorem voters_count_le_committee (E : Env V) (late : Finset (GoldfishVote V))
    (s : Slot) (hvalid : Protocol.VoteSetValid E s late) :
    Protocol.voters_count E late s ≤ (E.committee s).card := by
  rw [Protocol.voters_count,
    Protocol.raw_voters_count_eq_committee_voters_count hvalid,
    Protocol.committee_voters_count]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-! ## Safety: conflicting blocks cannot both clear the gate

The interface is one-directional about vote transfer and bilateral about
resolution. A vote counted by `v` either reaches `w` by `w`'s late cutoff, or
`w` already holds two distinct votes from that validator. In the second case,
`w` rejects the relayed vote at the protocol's two-vote cap, but the validator
already counts in `w`'s denominator and cannot count in `w`'s numerator.
`Sync.lean` discharges transfer from `t_GST = 0`, strict relay, and the handler
guards; nothing here knows about time. -/

/-- What one node's confirmation count needs to know about another's
(PROTOCOL.md#the-complete-protocol).

Two clauses, both about a vote `v` counted at the support cutoff:

* `transfer` — `w` holds it by its own confirmation cutoff, or already identifies
  its validator as an equivocator. The disjunction is necessary because
  `on_goldfish_vote` keeps at most two distinct votes per validator and can
  reject the relayed vote itself after the cap has fired.
* `resolve` — if both processed trees resolve its target root, their answers are
  the same block. Root collisions are the only way this can fail, and they are
  exactly what run-wide `RootCollisionFree` and scoped `RootInjectiveBelow`
  exclude. This clause does not claim that receipt of a raw vote makes its head
  arrive. -/
structure CrossView (Tv Tw : Finset (Block V)) (votesv latew : Finset (GoldfishVote V)) :
    Prop where
  /-- A counted vote reaches the other late view, or that view already holds an
  equivocation by the vote's validator. -/
  transfer : ∀ u ∈ votesv,
    u ∈ latew ∨ Protocol.equivocates latew u.val_index = true
  /-- The two trees agree whenever both resolve a counted vote's target. -/
  resolve : ∀ u ∈ votesv, ∀ B C : Block V,
    Block.find? Tv u.head = some B → Block.find? Tw u.head = some C → B = C

namespace CrossView

omit [Fintype V] in
/-- Build cross-view agreement from its two independent causes.

`transfer` is the raw-vote delivery fact after accounting for the receiver's
two-vote cap. Run-wide hash collision freedom supplies resolution coherence. No
target-arrival premise is needed: unresolved votes remain in the denominator
but support no block. -/
theorem of_rootInjective {Tv Tw : Finset (Block V)}
    {votesv latew : Finset (GoldfishVote V)}
    (transfer : ∀ u ∈ votesv,
      u ∈ latew ∨ Protocol.equivocates latew u.val_index = true)
    (root_injective : RootInjectiveBelow (Tv ∪ Tw)) :
    CrossView Tv Tw votesv latew := by
  refine ⟨transfer, ?_⟩
  intro u _ B C hfindB hfindC
  have hBroot : B.root = u.head := by
    unfold Block.find? pickUnique? at hfindB
    split at hfindB
    · rename_i hex
      rw [Option.some_inj] at hfindB
      subst hfindB
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfindB (by simp)
  have hCroot : C.root = u.head := by
    unfold Block.find? pickUnique? at hfindC
    split at hfindC
    · rename_i hex
      rw [Option.some_inj] at hfindC
      subst hfindC
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfindC (by simp)
  apply root_injective B C
  · exact ⟨B, Finset.mem_union_left Tw (Proofs.Engine.pickUnique?_mem hfindB),
      Block.preceq_self B⟩
  · exact ⟨C, Finset.mem_union_right Tv (Proofs.Engine.pickUnique?_mem hfindC),
      Block.preceq_self C⟩
  · exact hBroot.trans hCroot.symm

end CrossView

/-- Supporters of conflicting blocks, counted at two different nodes, are
disjoint: a validator counted at both has **one** vote, and one vote cannot
descend from two conflicting blocks (PROTOCOL.md#the-complete-protocol). -/
theorem supporters_disjoint_cross {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hconf : Block.compatible C D = false) :
    Disjoint (Protocol.goldfishSupporters E Tv votesv votesv s C)
      (Protocol.goldfishSupporters E Tw votesw votesw s D) := by
  rw [Finset.disjoint_left]
  intro x hxC hxD
  rw [mem_supporters_iff] at hxC hxD
  obtain ⟨-, u, hu, -, htarC⟩ := hxC
  obtain ⟨-, u', hu', -, htarD⟩ := hxD
  rw [Protocol.votes_by, Finset.mem_filter] at hu hu'
  have hsame : u = u' := by
    rcases hvw.transfer u hu.1 with hreach | hequiv
    · exact hNw.unique_in_late hu'.1 hreach (by rw [hu.2, hu'.2])
    · have hclean := hNw.no_equivocation_in_late hu'.1
      rw [hu'.2] at hclean
      rw [hu.2, hclean] at hequiv
      simp at hequiv
  obtain ⟨B₁, hfind₁, hpre₁⟩ := targets_under_iff.mp htarC
  obtain ⟨B₂, hfind₂, hpre₂⟩ := targets_under_iff.mp htarD
  have hblocks : B₁ = B₂ := by
    apply hvw.resolve u hu.1 B₁ B₂ hfind₁
    simpa only [hsame] using hfind₂
  have : B₂ = B₁ := hblocks.symm
  subst this
  exact absurd (Block.compatible_of_preceq_common hpre₁.2 hpre₂.2) (by rw [hconf]; simp)

/-- A source supporter participates in the target late view. Either its exact
vote arrived, or the target already holds two votes by the same validator. -/
theorem supporters_subset_participants_cross {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv latew : Finset (GoldfishVote V)} {s : Slot} {C : Block V}
    (hvw : CrossView Tv Tw votesv latew) :
    Protocol.goldfishSupporters E Tv votesv votesv s C ⊆ Protocol.participants E latew s := by
  intro x hx
  rw [mem_supporters_iff] at hx
  obtain ⟨-, u, hu, -, -⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  rcases hvw.transfer u hu.1 with hreach | hequiv
  · refine Finset.card_pos.mpr ⟨u, ?_⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach, hu.2⟩
  · rw [Protocol.equivocates, decide_eq_true_eq] at hequiv
    rw [hu.2] at hequiv
    omega

/-- The two supporter sets together fit inside `w`'s participants: they are
disjoint and both sit under `w`'s late cutoff. -/
theorem card_supporters_add_le {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hconf : Block.compatible C D = false) :
    (Protocol.goldfishSupporters E Tv votesv votesv s C).card +
        (Protocol.goldfishSupporters E Tw votesw votesw s D).card ≤
      Protocol.voters_count E latew s := by
  have hdisj : Disjoint (Protocol.goldfishSupporters E Tv votesv votesv s C)
      (Protocol.goldfishSupporters E Tw votesw votesw s D) :=
    supporters_disjoint_cross hNw hvw hconf
  rw [← Finset.card_union_of_disjoint hdisj]
  refine Finset.card_le_card ?_
  refine Finset.union_subset ?_ ?_
  · exact supporters_subset_participants_cross hvw
  · exact supporters_subset_participants E Tw hNw.subset_late s D

/-- **The safety core** (PROTOCOL.md#the-complete-protocol). Two blocks that clear the
confirmation gate at two honest nodes, in the same slot, are compatible.

The whole proof is `2(a + b) ≤ count_v + count_w < 2a + 2b`. No honest
committee, no honest weight, no fault bound: the gate is a strict majority of a
denominator that both nodes' supporters fit inside, and the `no_second_vote_in`
filter is what makes the two supporter sets disjoint. -/
theorem eligible_compatible {E : Env V} {Tv Tw : Finset (Block V)}
    {earlyv latev votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNv : Numerator earlyv latev votesv)
    (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hwv : CrossView Tw Tv votesw latev)
    (hC : Protocol.voters_count E latev s < 2 * Protocol.goldfish_score E Tv votesv votesv s C)
    (hD : Protocol.voters_count E latew s < 2 * Protocol.goldfish_score E Tw votesw votesw s D) :
    Block.compatible C D = true := by
  by_contra hcon
  have hconf : Block.compatible C D = false := by simpa using hcon
  have hconf' : Block.compatible D C = false := by
    rw [Block.compatible, Bool.or_eq_false_iff]
    rw [Block.compatible, Bool.or_eq_false_iff] at hconf
    exact ⟨hconf.2, hconf.1⟩
  rw [hNv.score_eq_supporters] at hC
  rw [hNw.score_eq_supporters] at hD
  have h₁ := card_supporters_add_le (E := E) (s := s) hNw hvw hconf
  have h₂ := card_supporters_add_le (E := E) (s := s) hNv hwv hconf'
  omega

/-! ## Liveness: an honestly-proposed block clears the gate and its siblings do not -/

/-- Every honest committee member of slot `s` has a counted vote resolving to
`B` (rev. 3 §8, (ii); PROTOCOL.md#the-complete-protocol).

This is the conclusion of the synchrony argument — the proposal is held
everywhere by `t_s + Δ`, honest voters adopt it because `B.slot = Σ.s` makes it
eligible without a majority, and their votes are held everywhere by `t_s + 2Δ`,
so they land in `early` — packaged as the single premise the counting needs. -/
structure HonestSupport (E : Env V) (T : Finset (Block V))
    (votes : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (B : Block V) : Prop where
  /-- PROTOCOL.md#the-complete-protocol: `|K_s| < 2·|K_s ∩ H|`. -/
  majority : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card
  /-- Every honest committee member's counted slot-`s` vote resolves to `B`. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ votes, u.val_index = x ∧ u.slot = s ∧
    Block.find? T u.head = some B ∧ B.slot ≤ u.slot

namespace HonestSupport

variable {E : Env V} {T : Finset (Block V)}
  {early late votes : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V} {B : Block V}

/-- Every honest committee member supports every ancestor of `B`. -/
theorem subset_supporters (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) {C : Block V}
    (hC : Block.preceq C B = true) :
    (E.committee s) ∩ Hon ⊆ Protocol.goldfishSupporters E T votes votes s C := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, hfind, hBslot⟩ := h.vote x hx.1 hx.2
  rw [mem_supporters_iff]
  refine ⟨hN.no_equivocation x, u, ?_, hslot,
    targets_under_iff.mpr ⟨B, hfind, hBslot, hC⟩⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hu, hval⟩

/-- No honest committee member supports a block that does not precede `B`: their
one counted vote resolves to `B` itself. -/
theorem not_mem_supporters (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) {D : Block V}
    (hD : Block.preceq D B = false) {x : V} (hx : x ∈ E.committee s) (hxH : x ∈ Hon) :
    x ∉ Protocol.goldfishSupporters E T votes votes s D := by
  intro hmem
  rw [mem_supporters_iff] at hmem
  obtain ⟨-, u', hu', -, htar⟩ := hmem
  obtain ⟨u, hu, hval, -, hfind, -⟩ := h.vote x hx hxH
  rw [Protocol.votes_by, Finset.mem_filter] at hu'
  have hsame : u' = u := hN.unique_in_late hu (hN.subset_late hu'.1) (by rw [hu'.2, hval])
  obtain ⟨B', hfind', hpre⟩ := targets_under_iff.mp htar
  rw [hsame, hfind] at hfind'
  have : B' = B := by simpa using hfind'.symm
  subst this
  exact absurd hpre.2 (by rw [hD]; simp)

/-- The honest committee members are counted in the denominator. -/
theorem inter_subset_participants (h : HonestSupport E T votes s Hon B)
    (hsub : votes ⊆ late) : (E.committee s) ∩ Hon ⊆ Protocol.participants E late s := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, -, -, -⟩ := h.vote x hx.1 hx.2
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hsub hu, hval⟩

/-- **The gate clears at every ancestor of `B`** (PROTOCOL.md#the-complete-protocol):
`count ≤ |K_s| < 2·|K_s ∩ H| ≤ 2·score(C)`. -/
theorem eligible (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {C : Block V}
    (hC : Block.preceq C B = true) :
    Protocol.voters_count E late s < 2 * Protocol.goldfish_score E T votes votes s C := by
  have hscore : ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes votes s C := by
    rw [hN.score_eq_supporters]
    exact Finset.card_le_card (h.subset_supporters hN hC)
  have hcount := voters_count_le_committee E late s hvalid
  have := h.majority
  omega

/-- A block that does not precede `B` is supported only by Byzantine
participants. -/
theorem score_le_byz (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {D : Block V}
    (hD : Block.preceq D B = false) :
    Protocol.goldfish_score E T votes votes s D ≤
      ((Protocol.participants E late s) \ Hon).card := by
  rw [hN.score_eq_supporters]
  refine Finset.card_le_card ?_
  intro x hx
  have hx' := hx
  rw [mem_supporters_iff] at hx'
  refine Finset.mem_sdiff.mpr ⟨supporters_subset_participants E T hN.subset_late s D hx, ?_⟩
  intro hxH
  obtain ⟨-, u, hu, -, -⟩ := hx'
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  have hcommittee := (hvalid u (hN.subset_late hu.1)).2
  rw [hu.2] at hcommittee
  exact h.not_mem_supporters hN hD hcommittee hxH hx

/-- The Byzantine participants are fewer than the honest committee members
(PROTOCOL.md#the-complete-protocol). -/
theorem byz_lt (h : HonestSupport E T votes s Hon B)
    (hvalid : Protocol.VoteSetValid E s late) :
    ((Protocol.participants E late s) \ Hon).card < ((E.committee s) ∩ Hon).card := by
  have hsub : (Protocol.participants E late s) \ Hon ⊆ (E.committee s) \ Hon := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    have hx' : x ∈ Protocol.committee_participants E late s := by
      rw [← Protocol.raw_participants_eq_committee_participants hvalid]
      exact hx.1
    exact ⟨Finset.filter_subset _ _ hx', hx.2⟩
  have hcard : ((E.committee s) \ Hon).card =
      (E.committee s).card - ((E.committee s) ∩ Hon).card := by
    rw [Finset.card_sdiff, Finset.inter_comm]
  have hle := Finset.card_le_card hsub
  have hinter : ((E.committee s) ∩ Hon).card ≤ (E.committee s).card :=
    Finset.card_le_card Finset.inter_subset_left
  have := h.majority
  omega

/-- **Strict domination along the path** (PROTOCOL.md#the-complete-protocol). A block that
does not precede `B` scores strictly below every ancestor of `B`: the first is
supported only by Byzantine participants, the second by every honest committee
member, and the honest side is the larger. -/
theorem score_lt (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {C D : Block V}
    (hC : Block.preceq C B = true) (hD : Block.preceq D B = false) :
    Protocol.goldfish_score E T votes votes s D < Protocol.goldfish_score E T votes votes s C := by
  have h₁ := h.score_le_byz (late := late) hN hvalid hD
  have h₂ : ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes votes s C := by
    rw [hN.score_eq_supporters]
    exact Finset.card_le_card (h.subset_supporters hN hC)
  have h₃ := h.byz_lt (late := late) hvalid
  omega

/-- **The gate fails strictly below `B`** (PROTOCOL.md#the-complete-protocol). The
denominator holds the honest committee members *and* every Byzantine
participant, and the score is at most the latter, so `2·score ≤ count`. -/
theorem not_eligible (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {D : Block V}
    (hD : Block.preceq D B = false) :
    ¬ Protocol.voters_count E late s < 2 * Protocol.goldfish_score E T votes votes s D := by
  have h₁ := h.score_le_byz (late := late) hN hvalid hD
  have h₃ := h.byz_lt (late := late) hvalid
  have hsplit : ((E.committee s) ∩ Hon).card + ((Protocol.participants E late s) \ Hon).card ≤
      Protocol.voters_count E late s := by
    have hdisj : Disjoint ((E.committee s) ∩ Hon)
        ((Protocol.participants E late s) \ Hon) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
    rw [Protocol.voters_count, ← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_le_card (Finset.union_subset ?_ Finset.sdiff_subset)
    exact h.inter_subset_participants hN.subset_late
  omega

end HonestSupport

end Protocol
end DecoupledConsensusModel

end
