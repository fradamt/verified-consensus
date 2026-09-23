module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Main
public import DecoupledConsensusProofs.Protocol.Grades.Anchor
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Cones

The two tests a block gets against a set of vote targets: *below every target*,
which is what the majority clause needs, and *below none of them*, which is what
excludes a sibling. -/


omit [Fintype V] in
/-- `C ⪯ B` with `C ≠ B` means `C` precedes `B`'s parent: the walk's own step
relation, read backwards (PROTOCOL.md#the-complete-protocol). -/
theorem preceq_parent_of_ne {C B H : Block V} (hpar : B.parent? = some H)
    (hCB : Block.preceq C B = true) (hne : C ≠ B) : Block.preceq C H = true := by
  cases B with
  | genesis => simp [Block.parent?] at hpar
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at hpar
      subst hpar
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hCB
      rcases hCB with h | h
      · exact absurd h hne
      · exact h

/-- Every block the honest votes name descends from `C` — the test the majority
clause passes on. -/
def Under (tgt : Block V → Prop) (C : Block V) : Prop :=
  ∀ X : Block V, tgt X → Block.preceq C X = true

/-- No block the honest votes name descends from `D` — the test that leaves `D`
with Byzantine support alone. -/
def Off (tgt : Block V → Prop) (D : Block V) : Prop :=
  ∀ X : Block V, tgt X → Block.preceq D X = false

omit [Fintype V] in
/-- **`Off` from a depth bound.** A block that does not precede `B` and is no
deeper than `B` precedes no descendant of `B`: the two would be comparable, and
the depth decides which way (PROTOCOL.md#the-complete-protocol).

This is what turns "not on the path to `B`" into "unsupported" for every sibling
the walk meets, and it is the only place `Off` has to be established. -/
theorem off_of_depth {B D : Block V} (hD : Block.preceq D B = false)
    (hdep : D.depth ≤ B.depth) : Off (fun X => Block.Preceq B X) D := by
  intro X hBX
  rw [← Bool.not_eq_true]
  intro hDX
  rcases Block.preceq_linear hDX hBX with h | h
  · exact absurd h (by rw [hD]; simp)
  · have hEq : B = D := Block.preceq_eq_of_depth_le h hdep
    rw [← hEq] at hD
    exact absurd (Block.preceq_self B) (by rw [hD]; simp)



/-! ## 2. Honest support with the equivocators left in

The counting `Confirmation.lean` cannot do. Its `HonestSupport` routes every
bound through `Numerator.score_eq_supporters` — "with no equivocators the score is
the plain supporter count" — and the fork choice's merged view has equivocators in
it, both in the numerator (credited to every block) and in the denominator
(PROTOCOL.md#the-complete-protocol).

The fix is to count three disjoint sets instead of two: the equivocators, the
supporters of an off-cone block, and the honest committee members. Honest
validators equivocate in no view, so the third is disjoint from the first; a
supporter is by definition a non-equivocator, so the second is disjoint from the
first; and the third is disjoint from the second because an honest vote names a
block in the cone.

`late` is the denominator's vote set, which is the numerator's own set for the
fork choice and the wider `confLate` for confirmation. -/

/-- §2.4 an equivocator has two votes, so it participates (PROTOCOL.md#the-complete-protocol,
217–218). -/
theorem equivocators_subset_participants (E : Env V)
    {votes late : Finset (GoldfishVote V)} (hsub : votes ⊆ late) (s : Slot) :
    Protocol.equivocators E votes s ⊆ Protocol.participants E late s := by
  intro x hx
  simp only [Protocol.equivocators, Protocol.raw_equivocators, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hcard : 2 ≤ (Protocol.votes_by votes x).card := by
    have := hx
    rw [Protocol.equivocates, decide_eq_true_eq] at this
    exact this
  have hmono : (Protocol.votes_by votes x).card ≤ (Protocol.votes_by late x).card := by
    refine Finset.card_le_card ?_
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    exact ⟨hsub hu.1, hu.2⟩
  rw [Protocol.participates, decide_eq_true_eq]
  omega

/-- **Honest support for a cone of targets** (rev. 3 §8; PROTOCOL.md#the-complete-protocol,
373–374).

Four clauses, and each one is a run fact the synchrony argument delivers:

* `majority` — `|K_s| < 2·|K_s ∩ H|`, the counting assumption
  (PROTOCOL.md#the-complete-protocol);
* `counted` — the numerator sits inside the denominator, `early ⊆ late` for
  confirmation and `rfl` for the fork choice (PROTOCOL.md#the-complete-protocol);
* `no_equiv` — an honest committee member does not equivocate, so its vote is not
  credited to every block;
* `vote` — every honest committee member's slot-`s` vote is in the counted set and
  its target resolves, in this store's tree, to a block `tgt` admits.

`tgt` is a predicate rather than a block because O13 needs the *cone*: with a
Byzantine proposer the honest heads of the next slot need not agree, and
non-retreat does not ask them to. -/
structure ConeSupport (E : Env V) (T : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    (tgt : Block V → Prop) : Prop where
  /-- PROTOCOL.md#the-complete-protocol: `|K_s| < 2·|K_s ∩ H|`. -/
  majority : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card
  /-- The counted votes sit under the denominator's cutoff. -/
  counted : votes ⊆ late
  /-- The support half of the two-view pair is inside the raw half
  (baseline `7b2efec`: `support_votes ⊆ votes` is a stated property). -/
  sub : support ⊆ votes
  /-- An honest committee member does not equivocate in the **raw** set. -/
  no_equiv : ∀ x ∈ E.committee s, x ∈ Hon → Protocol.equivocates votes x = false
  /-- Every honest committee member's **support** slot-`s` vote names a target in
  the cone. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧
    ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X

namespace ConeSupport

variable {E : Env V} {T : Finset (Block V)}
  {votes support late : Finset (GoldfishVote V)}
  {s : Slot} {Hon : Finset V} {tgt : Block V → Prop}

/-- Every honest committee member supports every block the cone lies under. -/
theorem subset_supporters (h : ConeSupport E T votes support late s Hon tgt)
    {C : Block V} (hC : Under tgt C) :
    (E.committee s) ∩ Hon ⊆ Protocol.goldfishSupporters E T votes support s C := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, X, hfind, hXslot, htgt⟩ := h.vote x hx.1 hx.2
  rw [mem_supporters_iff]
  refine ⟨h.no_equiv x hx.1 hx.2, u, ?_, hslot,
    targets_under_iff.mpr ⟨X, hfind, hXslot, hC X htgt⟩⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hu, hval⟩

/-- The honest committee members are counted in the denominator. -/
theorem subset_participants (h : ConeSupport E T votes support late s Hon tgt) :
    (E.committee s) ∩ Hon ⊆ Protocol.participants E late s := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, -, -⟩ := h.vote x hx.1 hx.2
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨h.counted (h.sub hu), hval⟩

/-- **No honest committee member supports an off-cone block.** Its one raw vote
names a block the cone admits, and no such block descends from `D`. -/
theorem not_mem_supporters (h : ConeSupport E T votes support late s Hon tgt)
    {D : Block V}
    (hD : Off tgt D) {x : V} (hx : x ∈ E.committee s) (hxH : x ∈ Hon) :
    x ∉ Protocol.goldfishSupporters E T votes support s D := by
  intro hmem
  rw [mem_supporters_iff] at hmem
  obtain ⟨-, u', hu', -, htar⟩ := hmem
  obtain ⟨u, hu, hval, -, X, hfind, hXslot, htgt⟩ := h.vote x hx hxH
  have hcard : (Protocol.votes_by votes x).card ≤ 1 := by
    have hne := h.no_equiv x hx hxH
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hne
    omega
  have huin : u ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨h.sub hu, hval⟩
  have hu'raw : u' ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter] at hu' ⊢
    exact ⟨h.sub hu'.1, hu'.2⟩
  have hsame : u' = u := Finset.card_le_one.mp hcard u' hu'raw u huin
  obtain ⟨Y, hfindY, hpre⟩ := targets_under_iff.mp htar
  rw [hsame, hfind] at hfindY
  have hYX : Y = X := by simpa using hfindY.symm
  subst hYX
  exact absurd hpre.2 (by rw [hD Y htgt]; simp)

/-- **The three-set count** (PROTOCOL.md#the-complete-protocol). The
equivocators, an off-cone block's supporters, and the honest committee members are
pairwise disjoint participants, and the first two are exactly the off-cone score.

This is the bound `Confirmation.lean` gets for free from an empty equivocator set
and this file has to earn. -/
theorem score_add_le (h : ConeSupport E T votes support late s Hon tgt) {D : Block V}
    (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D + ((E.committee s) ∩ Hon).card ≤
      Protocol.voters_count E late s := by
  have hdisj1 : Disjoint (Protocol.equivocators E votes s)
      (Protocol.goldfishSupporters E T votes support s D) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Protocol.equivocators, Protocol.raw_equivocators, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rw [mem_supporters_iff] at hx'
    rw [hx'.1] at hx
    simp at hx
  have hdisj2 : Disjoint ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ((E.committee s) ∩ Hon) := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_union]
    rintro (hx' | hx')
    · simp only [Protocol.equivocators, Protocol.raw_equivocators,
        Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      rw [h.no_equiv x hx.1 hx.2] at hx'
      simp at hx'
    · exact h.not_mem_supporters hD hx.1 hx.2 hx'
  have hsub : ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ∪ ((E.committee s) ∩ Hon) ⊆
      Protocol.participants E late s := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) h.subset_participants
    · exact equivocators_subset_participants E h.counted s
    · exact supporters_subset_participants E T (subset_trans h.sub h.counted) s D
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1] at hcard
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.equivocators, Protocol.goldfishSupporters, Protocol.voters_count,
    Protocol.raw_voters_count, Protocol.participants] at hcard ⊢
  omega

/-- The denominator is below twice the honest committee count
(PROTOCOL.md#the-complete-protocol). -/
theorem count_lt (h : ConeSupport E T votes support late s Hon tgt) :
    Protocol.VoteSetValid E s late →
    Protocol.voters_count E late s < 2 * ((E.committee s) ∩ Hon).card := by
  intro hvalid
  have h1 := voters_count_le_committee E late s hvalid
  have h2 := h.majority
  omega

/-- A block the cone lies under scores at least the honest committee count. -/
theorem le_score (h : ConeSupport E T votes support late s Hon tgt) {C : Block V}
    (hC : Under tgt C) :
    ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes support s C := by
  have hle := Finset.card_le_card (h.subset_supporters hC)
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.goldfishSupporters] at hle ⊢
  omega

/-- **The majority clause fires under the cone** (PROTOCOL.md#the-complete-protocol). -/
theorem eligible (h : ConeSupport E T votes support late s Hon tgt) {C : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hC : Under tgt C) :
    Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count_lt hvalid
  have h2 := h.le_score hC
  omega

/-- **The majority clause fails off the cone** (PROTOCOL.md#the-complete-protocol). -/
theorem not_eligible (h : ConeSupport E T votes support late s Hon tgt) {D : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hD : Off tgt D) :
    ¬ Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s D := by
  have h1 := h.count_lt hvalid
  have h2 := h.score_add_le hD
  omega

/-- **Strict domination** (PROTOCOL.md#the-complete-protocol): an off-cone block scores below
every block the cone lies under. -/
theorem score_lt (h : ConeSupport E T votes support late s Hon tgt) {C D : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hC : Under tgt C) (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D <
      Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count_lt hvalid
  have h2 := h.score_add_le hD
  have h3 := h.le_score hC
  omega

/-- `Confirmation.lean`'s premise is this one at the exact target, in the
confirmation regime — the **self-pair** instance (`support = votes`). The two
are interchangeable, so the P3(a) store lemmas read off a `ConeSupport` without
restating anything. -/
theorem toHonestSupport {B : Block V}
    (h : ConeSupport E T votes votes late s Hon (fun X => X = B)) :
    HonestSupport E T votes s Hon B where
  majority := h.majority
  vote := by
    intro x hx hxH
    obtain ⟨u, hu, hval, hslot, X, hfind, hXslot, hXB⟩ := h.vote x hx hxH
    exact ⟨u, hu, hval, hslot, by rw [← hXB]; exact hfind,
      hXB ▸ hXslot⟩

end ConeSupport


/-! ## 3. The walk, three more facts

`Availability/Walk.lean` proves the descent lemma this file consumes
(`ghost_reaches`) and the domination form of the `argmax`. Three things it does
not have, all needed here. -/

omit [Fintype V] in
/-- **The unique eligible child is selected**, with no score comparison at all
(PROTOCOL.md#the-complete-protocol).

`argmax?_eq_some_of_dominates` asks for strict score domination, which the honest
proposal does not have: it carries no slot-`(s−1)` vote below it. What it has is
the gate — it is the only child the gate lets through — and `pickUnique?` commits
to a singleton without inspecting the order. -/
theorem argmax?_eq_some_of_unique {score : Block V → Nat} {children : Finset (Block V)}
    {C : Block V} (hC : C ∈ children) (huniq : ∀ D ∈ children, D = C) :
    Protocol.argmax? score children = some C := by
  refine pickUnique?_eq_some hC ?_ (fun a ha _ => huniq a ha)
  simp only [Protocol.is_best_in, decide_eq_true_eq]
  intro D hD
  rw [huniq D hD]
  simp [Protocol.outranks]


omit [Fintype V] in

/-- **The walk passes through a block it is driven to.** Same step hypothesis as
`ghost_walk_reaches`, weaker conclusion: the result descends from `target` rather
than being `target`.

This is O13's shape. Non-retreat does not need the next slot's evaluation to stop
at the confirmed block — only to get there, and it may go further. -/
theorem ghost_walk_passes {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    ∀ (n : Nat) (H : Block V), Block.Preceq anchor H → Block.Preceq H target →
      target.depth ≤ H.depth + n →
      Block.Preceq target (Protocol.ghost_walk tree score eligible n H) := by
  intro n
  induction n with
  | zero =>
      intro H _ hpre hd
      have hEq : H = target := Block.preceq_eq_of_depth_le hpre (by omega)
      simp only [Protocol.ghost_walk, hEq]
      exact Block.preceq_self _
  | succ n ih =>
      intro H hanch hpre hd
      by_cases hHt : H = target
      · subst hHt
        exact ghost_walk_preceq tree score eligible (n + 1) H
      · obtain ⟨C, hCs, hCp⟩ := hstep H hanch hpre hHt
        have hchild := ghost_step_child hCs
        have hdepth : C.depth = H.depth + 1 := depth_of_parent? hchild.2.1
        simp only [Protocol.ghost_walk, hCs]
        exact ih C (Block.preceq_trans hanch (preceq_of_parent? hchild.2.1)) hCp (by omega)

omit [Fintype V] in

/-- **The descent reaches at least `target`** (PROTOCOL.md#the-complete-protocol). The
`ghost_reaches` interface without the stopping condition. -/
theorem ghost_passes {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hpre : Block.Preceq anchor target)
    (hpath : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
      C ∈ tree)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    Block.Preceq target (Protocol.ghost anchor tree score eligible) :=
  ghost_walk_passes hstep tree.card anchor (Block.preceq_self _) hpre
    (path_card anchor target tree hpre hpath)

omit [Fintype V] in
/-- Compatibility gives ancestry in either orientation; terminality upgrades it
to exact equality. `hforward` is used only when the anchor precedes `B`. -/
theorem ghost_eq_of_compatible_anchor_and_terminal
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A B : Block V}
    (hcompat : Block.compatible A B = true)
    (hforward : Block.Preceq A B →
      Block.Preceq B (Protocol.ghost A tree score eligible))
    (hanchorTerminal : Block.Preceq B A → A = B)
    (htreeTerminal : ∀ X ∈ tree, Block.Preceq B X → X = B) :
    Protocol.ghost A tree score eligible = B := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hAB | hBA
  · have hBhead := hforward hAB
    rcases Proofs.Records.ghost_mem A tree score eligible with hhead | hmem
    · rw [hhead] at hBhead ⊢
      exact Block.preceq_antisymm hAB hBhead
    · exact htreeTerminal _ hmem hBhead
  · have hBhead := Block.preceq_trans hBA
      (ghost_preceq A tree score eligible)
    rcases Proofs.Records.ghost_mem A tree score eligible with hhead | hmem
    · rw [hhead, hanchorTerminal hBA]
    · exact htreeTerminal _ hmem hBhead

/-! ## 4. The §5 gate, clause by clause (PROTOCOL.md#the-complete-protocol) -/

/-- §5.2 the final gate's three clauses, named (PROTOCOL.md#the-complete-protocol). -/
theorem goldfish_eligible_iff (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V) :
    Protocol.goldfish_eligible E σ h_max T cur votes support_votes s B = true ↔
      ((σ B.parent).h < h_max - 1 ∨
        Protocol.voters_count E votes s <
          2 * Protocol.goldfish_score E T votes support_votes s B ∨
        B.slot = cur) := by
  simp only [Protocol.goldfish_eligible, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-- §5.2 the current-slot exemption: a proposal of the current slot passes the
gate with no votes at all (PROTOCOL.md#the-complete-protocol). -/
theorem goldfish_eligible_current (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    {B : Block V} (hB : B.slot = cur) :
    Protocol.goldfish_eligible E σ h_max T cur votes support_votes s B = true := by
  rw [goldfish_eligible_iff]
  exact Or.inr (Or.inr hB)




/-! ## 5. The head at the vote instant is the proposal — O12's core -/






/-- **O13's core — the walk reaches the confirmed block** (row W5.17's H3,
cross-slot half; PROTOCOL.md#the-complete-protocol).

Every honest committee member's counted slot-`s` vote resolves *somewhere below*
`B`, and that is enough: at each step the child on the path to `B` is the only
eligible child, because a sibling is no deeper than `B` and off the path, hence
outside the cone (`off_of_depth`). The walk therefore descends at least to `B` and
may go further — which is exactly what non-retreat asks.

The gate here is §7.2's, the plain strict majority: available confirmation "uses
neither the candidate tree, the SG root, nor the height filter"
(PROTOCOL.md#the-complete-protocol), so neither `AtFrontier` nor `SoleCurrent` appears. -/
theorem ghost_passes_cone (E : Env V) (T tree : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    {A B : Block V}
    (hsup : ConeSupport E T votes support late s Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E s late)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B (Protocol.ghost A tree (Protocol.goldfish_score E T votes support s)
      (fun C => decide (Protocol.voters_count E late s <
        2 * Protocol.goldfish_score E T votes support s C))) := by
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C := by
    intro X hX
    exact Block.preceq_trans hCB hX
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_unique ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    exact ⟨hCmem, hCpar, by
      simp only [decide_eq_true_eq]
      exact hsup.eligible hvalid hUnder⟩
  · intro D hD
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    obtain ⟨-, hDpar, hDel⟩ := hD
    simp only [decide_eq_true_eq] at hDel
    have hDB : Block.preceq D B = true := by
      by_contra hcon
      have hfalse : Block.preceq D B = false := by simpa using hcon
      have hdep : D.depth ≤ B.depth := by
        have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
        have h2 : Hd.depth < B.depth := by
          have h3 := Block.preceq_depth_le hHdB
          rcases Nat.lt_or_ge Hd.depth B.depth with h | h
          · exact h
          · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
        omega
      exact hsup.not_eligible hvalid (off_of_depth hfalse hdep) hDel
    exact child_towards_unique hCpar hDpar hCB hDB


/-! ## 7. The composed head (PROTOCOL.md#the-complete-protocol)

`alg:healing-head` is one anchor choice followed by one Goldfish walk. Naming the
anchor separates the two, so that `Anchor.lean`'s cone bound — which is a
statement about the anchor alone — meets the descent above without either side
knowing how the other is proved. -/


/-- §6.4 the anchor `get_head_hc` selects: the fresh SG root when it is valid, the
relative-majority root otherwise (PROTOCOL.md#the-complete-protocol).

Mirrors `Protocol.get_sg_root`'s anchor rule verbatim (a grade-1
block in `st.T` with none in the filtered tree sends the anchor to the FG root
itself, not the relative-majority walk), so the `rfl` below keeps holding. -/
noncomputable def healAnchor (E : Env V) (hc : HealConfig) (st : Protocol.HealingStore V) : Block V :=
  match Protocol.fresh_anchor E hc st (hc.round_of st.s) with
  | some A => A
  | none =>
    if (st.T.filter (fun B => Protocol.G1 E st.gradeView hc (hc.round_of st.s) B = true)).Nonempty
    then Protocol.get_fg_root st.toFG
    else
      Protocol.majority_fork_choice E st.sg_votes hc.η_SG st.T
        (Protocol.get_fg_root st.toFG)
        (Protocol.get_filtered_block_tree st.toFG) (hc.round_of st.s)

/-- **The collapse tripwire for baseline `6501c27`'s relayering**: `healAnchor`
is §6's `get_sg_root` at the current round, definitionally. §5 owns the function
and the single final `get_head_hc`; §6 redefines only this body, so the model's
one point of §6 difference — this anchor — is exactly the tex's, and the
`rfl` says the two never drift. -/
theorem healAnchor_eq_get_sg_root (E : Env V) (hc : HealConfig)
    (st : Protocol.HealingStore V) :
    healAnchor E hc st = Protocol.get_sg_root E hc st (hc.round_of st.s) :=
  rfl

/-- The frozen candidate tree the slot-`s` voter walks. Its processed-block
view determines the Goldfish child domain only; the Healing anchor, score, and
eligibility inputs remain the full store. -/
def voter_candidate_tree (E : Env V) (st : Protocol.HealingStore V) :
    Finset (Block V) :=
  Protocol.get_filtered_block_tree_from st.toFG
    (Protocol.voter_processed_block_tree E st.toFG.toSG.toGoldfishStore st.s)


/-- The same split under an arbitrary grade contract. `healAnchor` is the
fixed-contract anchor; the engine's duties read the contract built from the
tick's own prepared cache, and the walk below it is the same walk. -/
theorem get_head_in_tree_split_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.HealingStore V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) :
    Protocol.get_head_in_tree_with_layer contract E hc st tree votes support_votes k =
      Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s
        (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
        tree votes support_votes k :=
  rfl

/-- The proof-layer frozen voter tree is the cumulative protocol duty's tree,
definitionally. -/
theorem voter_candidate_tree_eq_protocol_voter_filtered_block_tree (E : Env V)
    (st : Protocol.Store V) :
    voter_candidate_tree E st.toHealing =
      Protocol.voter_filtered_block_tree E st st.s :=
  rfl


/-! ## 8. The vote instant, at one honest store

Everything `goldfish_vote` reads at `t_s + Δ`, packaged as the premise the run
level hands over. Each field is a store fact; the run's job is to establish them,
and this file's job is that they are enough. -/




/-- **Named twin of `VoteStoreExtends`**: the determinism residual observed at
the prepared vote read. The sole semantic field `head` is now the
contract-parametric `voterHeadAt`. -/
structure NamedVoteStoreExtends (S : Setup V) (ρ : Run V) (v : V) (s : Slot)
    (tree₀ : Finset (Block V)) (H : Block V) (B : NamedBlock V) : Prop where
  /-- The proposal belongs to the read's current slot (PROTOCOL.md#the-complete-protocol). -/
  cur : B.slot = (voteDutyRead S ρ v s).st.core.s
  /-- It extends the head (PROTOCOL.md#the-complete-protocol). -/
  parent : B.erase.parent? = some H
  /-- The frozen voter candidate tree is the proposer's, plus the proposal. -/
  tree : voterCandidateTreeAt S ρ v s = insert B.erase tree₀
  /-- The proposal is new. -/
  fresh : B.erase ∉ tree₀
  /-- and nothing yet builds on it. -/
  leaf : ∀ C ∈ tree₀, C.parent? ≠ some B.erase
  /-- **The residual**: the exact head over the full frozen voter tree is the
  proposal. -/
  head : voterHeadAt S ρ v s = B.erase




/-- **The vote names the proposal, with no hypothesis about slot `s−1`**, over
the engine's contract. The determinism counterpart of `goldfish_vote_eq_with`. -/
theorem goldfish_vote_eq_extends_with (S : Setup V) (ρ : Run V) (v : V) (s : Slot)
    {tree₀ : Finset (Block V)} {H : Block V} {B : NamedBlock V}
    (hal : NamedVoteStoreExtends S ρ v s tree₀ H B)
    (hcom : (S.node v).val_index ∈ S.E.committee (voteDutyRead S ρ v s).st.core.s) :
    (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (voteDutyRead S ρ v s).cache) S.E S.hc (S.node v)
        (voteDutyRead S ρ v s).st).2 =
      some ⟨(S.node v).val_index, (voteDutyRead S ρ v s).st.core.s, B.erase.root⟩ := by
  have hhead : Protocol.get_head_in_tree_with
      (NamedProfile.gradeContract (voteDutyRead S ρ v s).cache) S.E S.hc
      (voteDutyRead S ρ v s).st.core
      (Protocol.voter_filtered_block_tree S.E (voteDutyRead S ρ v s).st.core
        (voteDutyRead S ρ v s).st.core.s)
      (Protocol.voter_view S.E (voteDutyRead S ρ v s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S ρ v s).st.core.s)
      (Protocol.voter_support_view S.E (voteDutyRead S ρ v s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S ρ v s).st.core.s)
      ((voteDutyRead S ρ v s).st.core.s - 1) = B.erase := hal.head
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with,
    hhead, if_pos hcom]

/-! ## 9. O12 — `EvaluationReaches`

Two named run-level residuals, and the agreement argument between them. Neither
residual mentions a fork choice: the descent is a theorem now, and what is left is
the execution-layer bridge — which tick reads which store, and which stamps land
inside the numerator. -/



/- Part B retirement candidate 3: use
DecoupledConsensusModel.Proofs.HealingSurface.NamedHonestVotesName.
The previous command and context are frozen in n36-part-b-candidate/v1.
Consumer ports remain open; no alias or replacement proof is declared here. -/


/-- The honest slot-`s` votes counted at one node all name `B`, so the store meets
`live_confirmed_eq`'s support premise. This is where the residuals meet:
`NamedHonestVotesName` says what was emitted and named, and `ConfirmationTick`
says it was counted. -/
theorem honestSupport_of_names (S : Setup V) (ρ : Run V) (s : Slot) (B : Block V)
    (hcom : HonestCommittees S ρ.honest)
    (hvt : Proofs.HealingSurface.NamedHonestVotesName S ρ s B)
    {st : Protocol.Store V} (hfind : Block.find? st.T B.root = some B)
    (hcount : ∀ u : GoldfishVote V, u.slot = s → u.val_index ∈ ρ.honest →
      u.val_index ∈ S.E.committee s →
      ρ.emits S u.val_index (Object.gfVote u) (Protocol.vote_time S.E s) →
      u ∈ confVotes S.E st s) :
    HonestSupport S.E st.T (confVotes S.E st s) s ρ.honest B where
  majority := hcom s
  vote := by
    intro x hx hxH
    let u : GoldfishVote V := ⟨x, s, B.root⟩
    have hu : u ∈ confVotes S.E st s := hcount u rfl hxH hx (hvt x hxH hx)
    have huEarly : u ∈ confEarly S.E st s := by
      rw [confVotes, Finset.mem_filter] at hu
      exact hu.1
    rw [confEarly, beforeCutoff, Finset.mem_filter] at huEarly
    have hBslot : B.slot ≤ u.slot :=
      Protocol.head_slot_le_of_resolution_time hfind huEarly.2
    exact ⟨u, hu, rfl, rfl, hfind, hBslot⟩






/-- **The confirmation walk reaches `B` under the contract the engine used.**
The same argument as `update_confirmation_preceq`: `live_confirmed` depends on
the contract only through the anchor `A`, and `ghost_passes_cone` and
`ghost_eligible` both take `A` as a parameter. -/
theorem update_confirmation_preceq_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.Store V) (k : Slot) (Hon : Finset V)
    {B : Block V}
    (hsup : ConeSupport E st.T (confVotes E st k) (confVotes E st k)
      (confLate E st k) k Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E k (confLate E st k))
    (hpre : Block.Preceq (confAnchorWith contract E hc st) B)
    (hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract E hc st) C →
      C ≠ confAnchorWith contract E hc st → Block.Preceq C B →
      C ∈ confTree st) :
    Block.Preceq B
      (Protocol.update_confirmation_with contract E hc st k).live_confirmed := by
  have hwalk : Block.Preceq B (confWalkWith contract E hc st k) :=
    ghost_passes_cone E st.T (confTree st) (confVotes E st k)
      (confVotes E st k) (confLate E st k) k Hon hsup hvalid hpre hpath
  rw [update_confirmation_with_live_confirmed]
  split
  · exact hwalk
  · rename_i hnel
    exfalso
    rcases ghost_eligible (confAnchorWith contract E hc st) (confTree st)
      (confScore E st k) (confEligible E st k) with hA | hel
    · have hAB : confAnchorWith contract E hc st = B :=
        Block.preceq_antisymm hpre (hA ▸ hwalk)
      refine hnel ?_
      show confEligible E st k (confWalkWith contract E hc st k) = true
      have : confWalkWith contract E hc st k = B := hA.trans hAB
      rw [this]
      simp only [confEligible, decide_eq_true_eq, confCount, confScore]
      exact hsup.eligible hvalid (fun X hX => hX)
    · exact hnel hel



/-! ## 11. Anchor variance, at the protocol level

Honest anchors differ: `fresh_anchor` fires at some nodes and not at others, and
`majority_fork_choice` descends from each node's own fork-choice root. What
`Anchor.lean` gives is that every one of them lies in `Can`'s cone, and that is
enough — the premises of the descent all weaken as the anchor rises. -/





/-! ## 12. The propagation step — honest heads stay in the cone

What makes O13's premise self-perpetuating, and the reason the cross-slot case is
easier than the same-slot one rather than harder.

Once every honest slot-`s` vote names `B`, `B` carries a strict majority in every
later merged view, so the *fork choice* — not only the confirmation walk —
descends at least to `B`. Honest slot-`(s+1)` heads are therefore in `B`'s cone,
their votes name blocks in `B`'s cone, and the invariant reproduces itself.

**No gate premise is needed here.** The proposal's own descent had to argue that
siblings fail the gate, because the proposal carries no votes and cannot outscore
them. A block with full honest support behind it needs no such help: it strictly
outscores every sibling, so `argmax?` picks it even where the height clause has
let a sibling through. -/

/-- **The Goldfish walk reaches the cone's root** (PROTOCOL.md#the-complete-protocol,
768–774). Every honest committee member's vote in the merged view names a block at
or below `B`, so the walk descends at least to `B`.

Neither `AtFrontier` nor `SoleCurrent` appears: a sibling that the height clause
or the current-slot clause admits is still strictly outscored, and the `argmax`
decides on the score. -/
theorem goldfish_passes_cone (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V))
    (k : Slot) (Hon : Finset V) {A B : Block V}
    (hsup : ConeSupport E T votes support votes k Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E k votes)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support k) := by
  rw [Protocol.goldfish_fork_choice]
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C :=
    fun X hX => Block.preceq_trans hCB hX
  have hHdlt : Hd.depth < B.depth := by
    rcases Nat.lt_or_ge Hd.depth B.depth with h | h
    · exact h
    · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_dominates ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    refine ⟨hCmem, hCpar, ?_⟩
    rw [goldfish_eligible_iff]
    exact Or.inr (Or.inl (hsup.eligible hvalid hUnder))
  · intro D hD hDC
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    have hDpar := hD.2.1
    have hDB : Block.preceq D B = false := by
      rw [← Bool.not_eq_true]
      intro hcon
      exact hDC (child_towards_unique hCpar hDpar hCB hcon)
    have hdep : D.depth ≤ B.depth := by
      have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
      omega
    exact hsup.score_lt hvalid hUnder (off_of_depth hDB hdep)


omit [Fintype V] in
/-- Adding a block changes no other block's child set: the walk sees it only at
its own parent (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_children_insert_of_ne {tree : Finset (Block V)} {eligible : Block V → Bool}
    {B H X : Block V} (hpar : B.parent? = some H) (hne : X ≠ H) :
    Protocol.ghost_children (insert B tree) eligible X =
      Protocol.ghost_children tree eligible X := by
  rw [Protocol.ghost_children, Protocol.ghost_children, Finset.filter_insert, if_neg]
  rintro ⟨hp, -⟩
  rw [hpar, Option.some.injEq] at hp
  exact hne hp.symm

omit [Fintype V] in

/-- At its own parent, the added block is the **only** eligible child, when the
parent had none before (PROTOCOL.md#the-complete-protocol). This is the proposal's position
exactly: the proposer's walk blocked at `H` because nothing below `H` cleared the
gate, and `B` clears it on the current-slot clause alone. -/
theorem ghost_children_insert_self {tree : Finset (Block V)} {eligible : Block V → Bool}
    {B H : Block V} (hpar : B.parent? = some H) (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_children (insert B tree) eligible H = {B} := by
  rw [Protocol.ghost_children, Finset.filter_insert, if_pos ⟨hpar, helig⟩]
  have hempty : tree.filter (fun C => C.parent? = some H ∧ eligible C = true) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro C hC ⟨h1, h2⟩
    rw [hstop C hC h1] at h2
    simp at h2
  rw [hempty]
  simp

omit [Fintype V] in
/-- The step at the added block's parent commits to it. -/
theorem ghost_step_insert_self {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V} (hpar : B.parent? = some H)
    (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_step (insert B tree) score eligible H = some B := by
  rw [Protocol.ghost_step, ghost_children_insert_self hpar helig hstop]
  exact argmax?_eq_some_of_unique (by simp) (by simp)

omit [Fintype V] in

/-- The added block is a leaf, so the walk open items there. -/
theorem ghost_step_insert_leaf {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V} (hpar : B.parent? = some H)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) :
    Protocol.ghost_step (insert B tree) score eligible B = none := by
  refine ghost_step_none ?_
  intro C hC hCB
  rcases Finset.mem_insert.mp hC with hEq | hmem
  · exfalso
    rw [hEq, hpar, Option.some.injEq] at hCB
    have h1 := depth_of_parent? hpar
    rw [hCB] at h1
    omega
  · exact absurd hCB (hfresh C hmem)

omit [Fintype V] in
/-- **The walk extension.** A walk that returned `H` over `tree` returns `B` over
`insert B tree`, when `B` is a fresh eligible child of `H` and a leaf.

The two walks take the *same steps*: away from `H` the child sets are equal, at
`H` the added block is the only eligible child, and at `B` there is none. One more
unit of fuel is exactly what `insert` adds to `tree.card`. -/
theorem ghost_walk_insert {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V}
    (hpar : B.parent? = some H) (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) :
    ∀ (n : Nat) (X : Block V), Protocol.ghost_walk tree score eligible n X = H →
      Protocol.ghost_walk (insert B tree) score eligible (n + 1) X = B := by
  have hstepH : Protocol.ghost_step (insert B tree) score eligible H = some B :=
    ghost_step_insert_self hpar helig hstop
  have hstepB : Protocol.ghost_step (insert B tree) score eligible B = none :=
    ghost_step_insert_leaf hpar hfresh
  intro n
  induction n with
  | zero =>
      intro X hres
      simp only [Protocol.ghost_walk] at hres
      subst hres
      simp only [Protocol.ghost_walk, hstepH]
  | succ n ih =>
      intro X hres
      rw [Protocol.ghost_walk] at hres
      cases hs : Protocol.ghost_step tree score eligible X with
      | none =>
          rw [hs] at hres
          subst hres
          simp only [Protocol.ghost_walk, hstepH, hstepB]
      | some C =>
          rw [hs] at hres
          have hXH : X ≠ H := by
            intro hEq
            rw [hEq] at hs
            rw [ghost_step_none hstop] at hs
            exact absurd hs (by simp)
          have hs' : Protocol.ghost_step (insert B tree) score eligible X = some C := by
            rw [Protocol.ghost_step, ghost_children_insert_of_ne hpar hXH, ← Protocol.ghost_step]
            exact hs
          rw [Protocol.ghost_walk, hs']
          exact ih C hres

omit [Fintype V] in
/-- **The descent extension** (PROTOCOL.md#the-complete-protocol). No counting anywhere: the
walk goes one block further because the gate admits exactly one more child. -/
theorem ghost_insert_eq {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A B H : Block V}
    (hpar : B.parent? = some H) (helig : eligible B = true)
    (hnotin : B ∉ tree)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B)
    (hwalk : Protocol.ghost A tree score eligible = H) :
    Protocol.ghost A (insert B tree) score eligible = B := by
  rw [Protocol.ghost, Finset.card_insert_of_notMem hnotin]
  exact ghost_walk_insert hpar helig hstop hfresh tree.card A hwalk

/-- **The fork choice extension** (PROTOCOL.md#the-complete-protocol). The
current-slot clause is what makes the proposal eligible; nothing else is asked of
it. -/
theorem goldfish_fork_choice_insert_proposal (E : Env V) (σ : Block V → ChainState V)
    (h_max : Height) (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (k : Slot) {A B H : Block V}
    (hpar : B.parent? = some H) (hslot : B.slot = cur) (hnotin : B ∉ tree)
    (hstop : ∀ C ∈ tree, C.parent? = some H →
      Protocol.goldfish_eligible E σ h_max T cur votes support k C = false)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B)
    (hwalk : Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support k
      = H) :
    Protocol.goldfish_fork_choice E σ h_max T cur A (insert B tree) votes support k
      = B := by
  rw [Protocol.goldfish_fork_choice] at hwalk ⊢
  exact ghost_insert_eq hpar
    (goldfish_eligible_current E σ h_max T cur votes support k hslot) hnotin hstop
    hfresh hwalk

/-! ## 14. O12's liveness route with no hypothesis about slot `s−1`

`VoteStoreExtends` replaces `VoteStoreAligned`'s counting clause with the
determinism one. It names no committee, no honest set and no majority: the honest
proposer at slot `s` is the only proposer either statement mentions. -/

/-- **Residual A′ — the vote tick, determinism form.** The counterpart of
`VoteTick`, with `NamedVoteStoreAligned` replaced by `NamedVoteStoreExtends`.
Same shape, same execution content, and no committee or majority anywhere in
it. -/
def VoteTickExtends (S : Setup V) (ρ : Run V) (s : Slot) (B : NamedBlock V) : Prop :=
  ∀ v ∈ ρ.honest, v ∈ S.E.committee s →
    ∃ (tree₀ : Finset (Block V)) (H : Block V) (u : GoldfishVote V),
      let n := voteDutyRead S ρ v s
      n.st.core.s = s ∧
      NamedVoteStoreExtends S ρ v s tree₀ H B ∧
      (Protocol.NamedDuties.goldfish_vote_with
          (NamedProfile.gradeContract n.cache) S.E S.hc (S.node v) n.st).2 = some u ∧
      NamedRun.emits S ρ v (.gfVote u) (Protocol.vote_time S.E s)

/-- **The determinism route reaches the common interface.** With this, O12 goes
through `evaluationReaches_of_names` without any vote concentration at slot
`s−1` — which is what `Internal.ProposalConfirmedFrom` needs, since it constrains
only slot `s`'s own proposer. -/
theorem honestVotesName_of_extends (S : Setup V) (ρ : Run V) (s : Slot)
    (B : NamedBlock V) (hvt : VoteTickExtends S ρ s B) :
    Proofs.HealingSurface.NamedHonestVotesName S ρ s B.erase := by
  intro v hv hcom
  obtain ⟨tree₀, H, u, hslot, hal, hduty, hemit⟩ := hvt v hv hcom
  have hnode : (S.node v).val_index = v := S.node_val_index v
  have hcomx : (S.node v).val_index ∈
      S.E.committee (voteDutyRead S ρ v s).st.core.s := by
    rw [hnode, hslot]; exact hcom
  have hue := goldfish_vote_eq_extends_with S ρ v s hal hcomx
  rw [hduty, Option.some.injEq] at hue
  rw [hue, hnode, hslot] at hemit
  exact hemit

/-! ## 15. What the counting premise costs, machine-checked

The counting route asks that the honest slot-`(s−1)` votes in the merged view all
name one head. This section shows exactly what that demands and exhibits a
configuration where it fails, so the boundary between the two routes is on the
record rather than in prose. -/



/-! ### The premise demands that an honest vote of that slot exist

A second failure mode of the counting premise, independent of the split and
needing no adversarial schedule at all. `ConeSupport` does not merely constrain
the honest slot-`k` votes — it **asserts that they exist**, because its `majority`
clause makes `K_k ∩ Hon` nonempty and its `vote` clause then produces a counted
vote for each member.

At `k = 0` no such vote exists in any admissible run, honest and synchronous or
not: `on_tick`'s Goldfish duty is guarded by `0 < s` (PROTOCOL.md#the-complete-protocol), so an
emitted vote carries a positive slot, and `Unforgeable.unforgeable` and `carried_gf`
close the pool and carried routes into a merged view. Since
`VoteStoreAligned.merged` is read at committee slot `Σ.s − 1`, the target slot
`s = 1` reads committee slot `0` and the premise fails there for every run.

That matters for the repair, not only for the record: it rules out rescuing
`Availability/Final.lean`'s `VoteStoresAligned` with a side condition making
slot `s−1`'s proposer honest. Slot `1` has no slot-`0` votes to concentrate,
whoever proposed.

The run-level half is one step from here — `Alignment.emits_of_voteVisible` on
either half of the merged view, then `Alignment.emits_gfVote_shape`'s
`0 < S.E.slotOf t` against `u.slot = 0` — but `Optimistic/Alignment.lean` sits
*downstream* of this module, so it cannot be taken here without a cycle. The
store-level half below is the reusable part, and it is what that step consumes. -/

/-- **The counting premise asserts an honest vote of its slot.** Its `majority`
clause forces the honest committee to be nonempty and its `vote` clause then
produces that member's counted slot-`k` vote.

Stated for an arbitrary target predicate, so it applies to both instantiations.
At `k = 0` the conclusion is false in every admissible run, which refutes the
premise there without any reference to the split. -/
theorem coneSupport_exists_honest_vote {E : Env V} {T : Finset (Block V)}
    {votes support late : Finset (GoldfishVote V)} {k : Slot} {Hon : Finset V}
    {tgt : Block V → Prop} (h : ConeSupport E T votes support late k Hon tgt) :
    ∃ x ∈ E.committee k, x ∈ Hon ∧
      ∃ u ∈ support, u.val_index = x ∧ u.slot = k := by
  have hpos : 0 < ((E.committee k) ∩ Hon).card := by
    have := h.majority
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, -⟩ := h.vote x hx.1 hx.2
  exact ⟨x, hx.1, hx.2, u, hu, hval, hslot⟩

/-- §6.4 `get_head_hc` **is** the walk from `healAnchor` (PROTOCOL.md#the-complete-protocol).
Definitional: the two roots are alternatives and Goldfish runs once below
whichever is selected. -/
theorem get_head_split (E : Env V) (hc : HealConfig) (st : Protocol.HealingStore V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) :
    Protocol.get_head_hc E hc st votes support_votes k =
      Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s (healAnchor E hc st)
        (Protocol.get_filtered_block_tree st.toFG) votes support_votes k :=
  rfl

end Optimistic
end Proofs
end DecoupledConsensusModel

end
