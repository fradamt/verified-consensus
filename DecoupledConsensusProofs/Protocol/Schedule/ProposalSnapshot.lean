module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteStoreExtends

@[expose] public section

/-!
# Proposer-fixed Goldfish support snapshot

The final Section 7 proposal carries two views: every raw previous-slot vote
known to the proposer and the exact subset that was resolved at proposal time.
The voter unions both carried views with its older frozen views. The two-vote
pool cap means the resulting raw sets need not be equal: a voter can retain a
third Byzantine vote that the proposer rejected. Such an extra vote is
score-invisible when the proposer already identifies that validator as an
equivocator.

This file first states that pure algebra as `ScorePreservingViewExtension`.
The run-facing producer below it can therefore target the exact facts needed by
`Proofs.Optimistic.goldfish_fork_choice_congr_votes`, without claiming false set
equality and without adding a protocol mechanism.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Pure two-view algebra -/

/-- A target two-view pair extends a source pair without changing Goldfish
scores or participation. Exact source votes remain present. Every additional
raw or support vote belongs to a validator that already equivocates in the
source raw view. -/
structure ScorePreservingViewExtension
    (sourceRaw sourceSupport targetRaw targetSupport :
      Finset (GoldfishVote V)) : Prop where
  raw_subset : sourceRaw ⊆ targetRaw
  support_subset : sourceSupport ⊆ targetSupport
  raw_extra_equiv : ∀ u ∈ targetRaw, u ∉ sourceRaw →
    Protocol.equivocates sourceRaw u.val_index = true
  support_extra_equiv : ∀ u ∈ targetSupport, u ∉ sourceSupport →
    Protocol.equivocates sourceRaw u.val_index = true

namespace ScorePreservingViewExtension

variable {sourceRaw sourceSupport targetRaw targetSupport :
  Finset (GoldfishVote V)}

omit [Fintype V] in
/-- Equivocation detection is monotone under raw-set inclusion. -/
private theorem equivocates_mono
    {A B : Finset (GoldfishVote V)} (hAB : A ⊆ B) (x : V)
    (hA : Protocol.equivocates A x = true) :
    Protocol.equivocates B x = true := by
  rw [Protocol.equivocates, decide_eq_true_eq] at hA ⊢
  apply le_trans hA
  apply Finset.card_le_card
  intro u hu
  rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
  exact ⟨hAB hu.1, hu.2⟩

omit [Fintype V] in
/-- The source and target detect exactly the same equivocators. -/
theorem equivocates_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport) (x : V) :
    Protocol.equivocates sourceRaw x =
      Protocol.equivocates targetRaw x := by
  cases hs : Protocol.equivocates sourceRaw x with
  | true =>
      have ht := equivocates_mono h.raw_subset x hs
      simp only [ht]
  | false =>
      cases ht : Protocol.equivocates targetRaw x with
      | false => rfl
      | true =>
          have hby : Protocol.votes_by targetRaw x ⊆
              Protocol.votes_by sourceRaw x := by
            intro u hu
            rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
            refine ⟨?_, hu.2⟩
            by_contra hnot
            have he := h.raw_extra_equiv u hu.1 hnot
            rw [hu.2, hs] at he
            contradiction
          have hcard := Finset.card_le_card hby
          rw [Protocol.equivocates, decide_eq_true_eq] at ht
          rw [Protocol.equivocates, decide_eq_false_iff_not] at hs
          exact absurd (le_trans ht hcard) hs

omit [Fintype V] in
/-- The source and target represent exactly the same validators. -/
theorem participates_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport) (x : V) :
    Protocol.participates sourceRaw x =
      Protocol.participates targetRaw x := by
  cases hs : Protocol.participates sourceRaw x with
  | true =>
      rw [Protocol.participates, decide_eq_true_eq] at hs
      have hby : Protocol.votes_by sourceRaw x ⊆
          Protocol.votes_by targetRaw x := by
        intro u hu
        rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
        exact ⟨h.raw_subset hu.1, hu.2⟩
      have ht : Protocol.participates targetRaw x = true := by
        rw [Protocol.participates, decide_eq_true_eq]
        exact lt_of_lt_of_le hs (Finset.card_le_card hby)
      simp only [ht]
  | false =>
      cases ht : Protocol.participates targetRaw x with
      | false => rfl
      | true =>
          rw [Protocol.participates, decide_eq_true_eq] at ht
          obtain ⟨u, hu⟩ := Finset.card_pos.mp ht
          rw [Protocol.votes_by, Finset.mem_filter] at hu
          by_cases hus : u ∈ sourceRaw
          · have hs' : Protocol.participates sourceRaw x = true := by
              rw [Protocol.participates, decide_eq_true_eq]
              apply Finset.card_pos.mpr
              refine ⟨u, ?_⟩
              rw [Protocol.votes_by, Finset.mem_filter]
              exact ⟨hus, hu.2⟩
            rw [hs] at hs'
            contradiction
          · have he := h.raw_extra_equiv u hu.1 hus
            rw [hu.2] at he
            have hp : Protocol.participates sourceRaw x = true := by
              rw [Protocol.equivocates, decide_eq_true_eq] at he
              rw [Protocol.participates, decide_eq_true_eq]
              omega
            rw [hs] at hp
            contradiction

/-- The source and target have the same source-exact equivocator set. -/
theorem raw_equivocators_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport) :
    Protocol.raw_equivocators sourceRaw =
      Protocol.raw_equivocators targetRaw := by
  apply Finset.ext
  intro x
  simp only [Protocol.raw_equivocators, Finset.mem_filter,
    Finset.mem_univ, true_and, h.equivocates_eq x]

/-- The source and target have the same source-exact participant set. -/
theorem raw_participants_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport) :
    Protocol.raw_participants sourceRaw =
      Protocol.raw_participants targetRaw := by
  apply Finset.ext
  intro x
  simp only [Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and, h.participates_eq x]

/-- For every tree, slot, and candidate, the source and target supporter sets
are equal. -/
theorem supporters_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport)
    (E : Env V) (T : Finset (Block V)) (s : Slot) (B : Block V) :
    Protocol.goldfishSupporters E T sourceRaw sourceSupport s B =
      Protocol.goldfishSupporters E T targetRaw targetSupport s B := by
  apply Finset.ext
  intro x
  rw [mem_supporters_iff, mem_supporters_iff, h.equivocates_eq x]
  constructor
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    refine ⟨hclean, u, ?_, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨h.support_subset hu.1, hu.2⟩
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    by_cases huSource : u ∈ sourceSupport
    · refine ⟨hclean, u, ?_, hus, htarget⟩
      · rw [Protocol.votes_by, Finset.mem_filter]
        exact ⟨huSource, hu.2⟩
    · have he := h.support_extra_equiv u hu.1 huSource
      rw [hu.2, h.equivocates_eq x, hclean] at he
      contradiction

/-- The source and target have the same supporters across two trees when every
source-support vote resolves to the same side of every candidate in both
trees. Extra target-support votes do not contribute because their validators
already equivocate in the source raw view. -/
theorem supporters_eq_across_trees
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport)
    {sourceT targetT : Finset (Block V)}
    (htargets : ∀ u ∈ sourceSupport, ∀ C : Block V,
      Protocol.targets_under sourceT C u =
        Protocol.targets_under targetT C u)
    (E : Env V) (s : Slot) (B : Block V) :
    Protocol.goldfishSupporters E sourceT sourceRaw sourceSupport s B =
      Protocol.goldfishSupporters E targetT targetRaw targetSupport s B := by
  apply Finset.ext
  intro x
  rw [mem_supporters_iff, mem_supporters_iff, h.equivocates_eq x]
  constructor
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    refine ⟨hclean, u, ?_, hus, ?_⟩
    · rw [Protocol.votes_by, Finset.mem_filter]
      exact ⟨h.support_subset hu.1, hu.2⟩
    · rw [← htargets u hu.1 B]
      exact htarget
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    by_cases huSource : u ∈ sourceSupport
    · refine ⟨hclean, u, ?_, hus, ?_⟩
      · rw [Protocol.votes_by, Finset.mem_filter]
        exact ⟨huSource, hu.2⟩
      · rw [htargets u huSource B]
        exact htarget
    · have he := h.support_extra_equiv u hu.1 huSource
      rw [hu.2, h.equivocates_eq x, hclean] at he
      contradiction

/-- The target pair gives exactly the source Goldfish score on every block. -/
theorem goldfish_score_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport)
    (E : Env V) (T : Finset (Block V)) (s : Slot) (B : Block V) :
    Protocol.goldfish_score E T sourceRaw sourceSupport s B =
      Protocol.goldfish_score E T targetRaw targetSupport s B := by
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  rw [h.raw_equivocators_eq]
  have hsupp : Protocol.raw_supporters T sourceRaw sourceSupport s B =
      Protocol.raw_supporters T targetRaw targetSupport s B :=
    h.supporters_eq E T s B
  rw [hsupp]

/-- The target pair gives the source Goldfish score across two trees when the
trees resolve every source-support vote identically relative to every
candidate. -/
theorem goldfish_score_eq_across_trees
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport)
    {sourceT targetT : Finset (Block V)}
    (htargets : ∀ u ∈ sourceSupport, ∀ C : Block V,
      Protocol.targets_under sourceT C u =
        Protocol.targets_under targetT C u)
    (E : Env V) (s : Slot) (B : Block V) :
    Protocol.goldfish_score E sourceT sourceRaw sourceSupport s B =
      Protocol.goldfish_score E targetT targetRaw targetSupport s B := by
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  rw [h.raw_equivocators_eq]
  have hsupp : Protocol.raw_supporters sourceT sourceRaw sourceSupport s B =
      Protocol.raw_supporters targetT targetRaw targetSupport s B :=
    h.supporters_eq_across_trees htargets E s B
  rw [hsupp]

/-- The target raw view has exactly the source participation count. -/
theorem voters_count_eq
    (h : ScorePreservingViewExtension
      sourceRaw sourceSupport targetRaw targetSupport)
    (E : Env V) (s : Slot) :
    Protocol.voters_count E sourceRaw s =
      Protocol.voters_count E targetRaw s := by
  simp only [Protocol.voters_count, Protocol.raw_voters_count]
  rw [h.raw_participants_eq]

end ScorePreservingViewExtension

end Protocol
end DecoupledConsensusModel

end
