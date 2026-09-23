module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Confirmation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement

@[expose] public section

/-!
# Confirmation adoption by an ordinary Goldfish voter

Section 7 evaluates a slot from an early, clean support set and a later
participation set. The next ordinary Goldfish voters use a two-view pair:
their raw view decides participation and equivocation, while their support view
decides ancestry support. This module proves the pure counting step between
those two reads.

The result is stronger than ordinary eligibility. Every supporter counted by
the confirmation becomes a non-equivocating supporter in the target view, and
the target has no participants that were absent from the source late view.
Thus, a strict confirmation majority becomes a strict *plain-support* majority
at the target.

`AdoptionTransport` is the exact execution boundary for one confirmed block.
Its forward field uses the protocol's accepted-vote/two-vote-cap alternative
only for votes that support that block. This restriction is necessary: a
minority vote can name an unrelated block, and confirmation adoption never uses
that vote as support. Its reverse field is the relay needed to rule out a new
target equivocation and to compare the two denominators. A run-level producer
builds both fields from event-indexed, causal accepted forwarding.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Protocol (ChainState)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The accepted-forwarding interface -/

/-- The delivery and resolution facts that transfer one confirmation count to
one ordinary voter view.

`sourceVotes` is the confirmation numerator, `sourceLate` its denominator,
`targetVotes` the ordinary raw view, and `targetSupport` its resolved support
view.

The disjunctions match the final protocol's two-vote cap. A relayed vote can
be absent only when the receiver already holds two votes by that validator.
The reverse direction then shows that this second case is impossible for an
identity that survived the source confirmation's late equivocation filter. -/
structure AdoptionTransport (sourceTree targetTree : Finset (Block V))
    (sourceVotes sourceLate targetVotes targetSupport : Finset (GoldfishVote V))
    (B : Block V) : Prop where
  /-- A source vote that supports `B` keeps both its vote and ancestry support
  at the target, or the target has already detected an equivocation by its
  validator. Minority votes on unrelated branches are deliberately outside
  this field. -/
  forward : ∀ u ∈ sourceVotes,
    Protocol.targets_under sourceTree B u = true →
      (u ∈ targetSupport ∧ Protocol.targets_under targetTree B u = true) ∨
        Protocol.equivocates targetVotes u.val_index = true
  /-- Every target raw vote reaches the source late view, or the source has
  already detected an equivocation by its validator. -/
  backward : ∀ u ∈ targetVotes,
    u ∈ sourceLate ∨ Protocol.equivocates sourceLate u.val_index = true

namespace AdoptionTransport

variable {sourceTree targetTree : Finset (Block V)}
  {sourceVotes sourceEarly sourceLate targetVotes targetSupport : Finset (GoldfishVote V)}
  {B : Block V}

omit [Fintype V] in
/-- A validator whose counted source vote survived the late filter cannot
equivocate in the target raw view.

If the target held two votes by that validator, reverse accepted forwarding
would put both in the source late view (or report an equivocation there). Both
alternatives contradict the source numerator's uniqueness. -/
theorem target_not_equivocates
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) {u : GoldfishVote V} (hu : u ∈ sourceVotes) :
    Protocol.equivocates targetVotes u.val_index = false := by
  have hcard : (Protocol.votes_by targetVotes u.val_index).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [Protocol.votes_by, Finset.mem_filter] at ha hb
    have vote_eq_source : ∀ {x : GoldfishVote V}, x ∈ targetVotes →
        x.val_index = u.val_index → x = u := by
      intro x hx hval
      rcases hT.backward x hx with hreach | hequiv
      · exact hN.unique_in_late hu hreach hval
      · have hclean := hN.no_equivocation_in_late hu
        rw [hval, hclean] at hequiv
        simp at hequiv
    exact (vote_eq_source ha.1 ha.2).trans (vote_eq_source hb.1 hb.2).symm
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  omega

/-- Every source confirmation supporter becomes a target ordinary supporter. -/
theorem supporters_subset
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) (E : Env V) (s : Slot) :
    Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B ⊆
      Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B := by
  intro x hx
  rw [mem_supporters_iff] at hx ⊢
  obtain ⟨-, u, hu, hslot, htarget⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  have hclean := hT.target_not_equivocates hN hu.1
  have hcleanX : Protocol.equivocates targetVotes x = false := by
    simpa only [hu.2] using hclean
  rcases hT.forward u hu.1 htarget with hreach | hequiv
  · refine ⟨hcleanX, u, ?_, hslot, hreach.2⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach.1, hu.2⟩
  · rw [hclean] at hequiv
    simp at hequiv

/-- Every target participant was already a source late participant.

An exact relayed vote supplies participation directly. In the cap branch the
source holds at least two votes, which also supplies participation. -/
theorem participants_subset
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) (E : Env V) (s : Slot) :
    Protocol.participants E targetVotes s ⊆ Protocol.participants E sourceLate s := by
  intro x hx
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx ⊢
  rw [Protocol.participates, decide_eq_true_eq] at hx ⊢
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  rcases hT.backward u hu.1 with hreach | hequiv
  · refine Finset.card_pos.mpr ⟨u, ?_⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach, hu.2⟩
  · rw [Protocol.equivocates, decide_eq_true_eq] at hequiv
    rw [hu.2] at hequiv
    omega

end AdoptionTransport

/-! ## Strict-majority adoption -/

/-- **Confirmation-to-next-view adoption.** If `B` clears the clean
confirmation gate at the source, then its source supporters inject into the
target ordinary supporters and form a strict majority of the target raw
participants.

This theorem uses no honesty or fault threshold. Those assumptions construct
honest votes elsewhere; the adoption step itself is relay, root resolution,
and strict-majority arithmetic. -/
theorem confirmation_adoption
    {E : Env V} {sourceTree targetTree : Finset (Block V)}
    {sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)} {s : Slot} {B : Block V}
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : Protocol.voters_count E sourceLate s <
      2 * Protocol.goldfish_score E sourceTree sourceVotes sourceVotes s B) :
    Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B ⊆
        Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B ∧
      Protocol.voters_count E targetVotes s <
        2 * (Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B).card := by
  have hsupport := AdoptionTransport.supporters_subset hN hT E s
  have hsupport_card := Finset.card_le_card hsupport
  have hparticipants := Finset.card_le_card
    (AdoptionTransport.participants_subset hT E s)
  have hparticipants' : Protocol.voters_count E targetVotes s ≤
      Protocol.voters_count E sourceLate s := by
    simpa only [Protocol.voters_count] using hparticipants
  have hsource : Protocol.voters_count E sourceLate s <
      2 * (Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B).card := by
    simpa only [hN.score_eq_supporters] using heligible
  exact ⟨hsupport, by omega⟩


/-! ## A genuine Section 7 evaluation -/

/-- A store evaluation genuinely confirms `B`: the selected live value is `B`
and the composed walk passed the confirmation gate. The second clause excludes
the specified root fallback. -/
structure GenuineConfirmation (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) (B : Block V)
    (contract : Protocol.GradeContract V) : Prop where
  selected : (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B
  genuine : confEligible E st s (confWalkWith contract E hc st s) = true

namespace GenuineConfirmation

/-- A genuine selected value is the walk itself. -/
theorem walk_eq {E : Env V} {hc : Protocol.HealConfig} {st : Protocol.Store V}
    {s : Slot} {B : Block V} {contract : Protocol.GradeContract V}
    (h : GenuineConfirmation E hc st s B (contract := contract)) :
    confWalkWith contract E hc st s = B := by
  have hselected := h.selected
  rw [update_confirmation_with_live_confirmed, if_pos h.genuine] at hselected
  exact hselected

/-- The selected block clears the source confirmation's strict-majority gate. -/
theorem eligible {E : Env V} {hc : Protocol.HealConfig} {st : Protocol.Store V}
    {s : Slot} {B : Block V} {contract : Protocol.GradeContract V}
    (h : GenuineConfirmation E hc st s B (contract := contract)) :
    Protocol.voters_count E (confLate E st s) s <
      2 * Protocol.goldfish_score E st.T (confVotes E st s) (confVotes E st s) s B := by
  have hg := h.genuine
  simp only [confEligible, decide_eq_true_eq, confCount, confScore] at hg
  simpa only [h.walk_eq] using hg

end GenuineConfirmation

/-! ## Ordinary-walk capture -/

/-- In one two-view Goldfish score, supporters of conflicting blocks are
disjoint. The raw view's non-equivocation test makes every support vote by the
shared identity unique; `support ⊆ votes` then puts both candidates' witnesses
under that same test. -/
theorem supporters_disjoint_of_conflicts
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B D : Block V}
    (hsub : support ⊆ votes) (hconflict : Block.compatible B D = false) :
    Disjoint (Protocol.goldfishSupporters E T votes support s B)
      (Protocol.goldfishSupporters E T votes support s D) := by
  rw [Finset.disjoint_left]
  intro x hxB hxD
  rw [mem_supporters_iff] at hxB hxD
  obtain ⟨hclean, u, hu, -, htargetB⟩ := hxB
  obtain ⟨-, u', hu', -, htargetD⟩ := hxD
  rw [Protocol.votes_by, Finset.mem_filter] at hu hu'
  have hcard : (Protocol.votes_by votes x).card ≤ 1 := by
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hclean
    omega
  have huRaw : u ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hsub hu.1, hu.2⟩
  have huRaw' : u' ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hsub hu'.1, hu'.2⟩
  have hs : u' = u := Finset.card_le_one.mp hcard u' huRaw' u huRaw
  obtain ⟨CB, hfindB, hpreB⟩ := targets_under_iff.mp htargetB
  obtain ⟨CD, hfindD, hpreD⟩ := targets_under_iff.mp htargetD
  rw [hs, hfindB] at hfindD
  have hEq : CD = CB := by simpa using hfindD.symm
  subst hEq
  exact absurd (Block.compatible_of_preceq_common hpreB.2 hpreD.2)
    (by rw [hconflict]; simp)

/-- An off-chain score and the plain supporters of a conflicting block fit
together inside the raw participant set. Equivocators are part of the
off-chain score and are disjoint from every supporter by definition. -/
theorem score_add_supporters_le
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B D : Block V}
    (hsub : support ⊆ votes) (hconflict : Block.compatible B D = false) :
    Protocol.goldfish_score E T votes support s D +
        (Protocol.goldfishSupporters E T votes support s B).card ≤
      Protocol.voters_count E votes s := by
  have hdisjScore : Disjoint (Protocol.equivocators E votes s)
      (Protocol.goldfishSupporters E T votes support s D) := by
    rw [Finset.disjoint_left]
    intro x hxEq hxD
    simp only [Protocol.equivocators, Protocol.raw_equivocators,
      Finset.mem_filter, Finset.mem_univ, true_and] at hxEq
    rw [mem_supporters_iff] at hxD
    rw [hxD.1] at hxEq
    simp at hxEq
  have hdisjCandidates : Disjoint
      (Protocol.goldfishSupporters E T votes support s B)
      (Protocol.goldfishSupporters E T votes support s D) :=
    supporters_disjoint_of_conflicts (E := E) (T := T) (s := s) hsub hconflict
  have hdisjAll : Disjoint
      ((Protocol.equivocators E votes s) ∪
        (Protocol.goldfishSupporters E T votes support s D))
      (Protocol.goldfishSupporters E T votes support s B) := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    rw [Finset.mem_union] at hx
    rcases hx with hxEq | hxD
    · have hclean := (mem_supporters_iff.mp hxB).1
      simp only [Protocol.equivocators, Protocol.raw_equivocators,
        Finset.mem_filter, Finset.mem_univ, true_and] at hxEq
      rw [hclean] at hxEq
      simp at hxEq
    · exact (Finset.disjoint_left.mp hdisjCandidates) hxB hxD
  have hparticipants :
      ((Protocol.equivocators E votes s) ∪
        (Protocol.goldfishSupporters E T votes support s D)) ∪
          (Protocol.goldfishSupporters E T votes support s B) ⊆
        Protocol.participants E votes s := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
    · exact Proofs.Optimistic.equivocators_subset_participants E (Finset.Subset.rfl) s
    · exact supporters_subset_participants E T hsub s D
    · exact supporters_subset_participants E T hsub s B
  have hcard := Finset.card_le_card hparticipants
  rw [Finset.card_union_of_disjoint hdisjAll,
    Finset.card_union_of_disjoint hdisjScore] at hcard
  rw [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.voters_count, Protocol.raw_voters_count]
  exact hcard

/-- A strict plain-support majority for `B` makes every block on `B`'s path
strictly outscore a conflicting block. This remains true with equivocations:
each equivocator is credited to both sides, while the strict majority is a set
of non-equivocating supporters. -/
theorem score_lt_of_supporter_majority
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B C D : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hCB : Block.preceq C B = true)
    (hconflict : Block.compatible B D = false) :
    Protocol.goldfish_score E T votes support s D <
      Protocol.goldfish_score E T votes support s C := by
  have hfit := score_add_supporters_le (E := E) (T := T) (s := s) hsub hconflict
  have hmono := Finset.card_le_card (supporters_mono E T votes support s hCB)
  have hbelow : Protocol.goldfish_score E T votes support s D <
      (Protocol.goldfishSupporters E T votes support s B).card := by
    omega
  have habove : (Protocol.goldfishSupporters E T votes support s C).card ≤
      Protocol.goldfish_score E T votes support s C := by
    rw [Protocol.goldfish_score, Protocol.raw_goldfish_score, Protocol.goldfishSupporters]
    omega
  omega

/-- A strict plain-support majority makes every ancestor of `B` pass the
ordinary majority clause. -/
theorem eligible_of_supporter_majority
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B C : Block V}
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hCB : Block.preceq C B = true) :
    Protocol.voters_count E votes s <
      2 * Protocol.goldfish_score E T votes support s C := by
  have hmono := Finset.card_le_card (supporters_mono E T votes support s hCB)
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.goldfishSupporters] at hmajority hmono ⊢
  omega

/-- **Adopted ordinary-walk capture.** If the ordinary view gives `B` a strict
plain-support majority, a composed Section 7 Goldfish walk whose anchor is
above `B` and whose candidate tree contains that path must pass through `B`.

The height and current-slot eligibility clauses need no extra invariant. They
can accept an off-path sibling, but the adopted majority makes the path child
strictly outscore every such sibling. -/
theorem goldfish_fork_choice_passes_supporter_majority
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
      C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s) := by
  rw [Protocol.goldfish_fork_choice]
  refine Proofs.Optimistic.ghost_passes hAB hpath ?_
  intro H hAH hHB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHB hne
  have hAC : Block.Preceq A C :=
    Block.preceq_trans hAH (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = H.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ H.depth := Block.preceq_depth_le hAH
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hHlt : H.depth < B.depth := by
    rcases Nat.lt_or_ge H.depth B.depth with h | h
    · exact h
    · exact absurd (Block.preceq_eq_of_depth_le hHB h) hne
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_dominates ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    refine ⟨hCmem, hCpar, ?_⟩
    rw [Proofs.Optimistic.goldfish_eligible_iff]
    exact Or.inr (Or.inl (eligible_of_supporter_majority hmajority hCB))
  · intro D hD hDC
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    have hDpar := hD.2.1
    have hDB : Block.preceq D B = false := by
      rw [← Bool.not_eq_true]
      intro hpre
      exact hDC (child_towards_unique hCpar hDpar hCB hpre)
    have hDdepth : D.depth ≤ B.depth := by
      rw [depth_of_parent? hDpar]
      omega
    have hBD : Block.preceq B D = false := by
      rw [← Bool.not_eq_true]
      intro hpre
      have hEq : B = D := Block.preceq_eq_of_depth_le hpre hDdepth
      rw [← hEq] at hDB
      exact absurd (Block.preceq_self B) (by rw [hDB]; simp)
    have hconflict : Block.compatible B D = false := by
      simp only [Block.compatible, Bool.or_eq_false_iff]
      exact ⟨hBD, hDB⟩
    exact score_lt_of_supporter_majority hsub hmajority hCB hconflict

/-- Capture needs only anchor compatibility. If the anchor is above `B`, the
majority drives the walk through the path. If the anchor already descends from
`B`, every later walk step remains a descendant of `B` without another counting
argument. -/
theorem goldfish_fork_choice_captures_supporter_majority
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s) := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompatible
  rcases hcompatible with hAB | hBA
  · exact goldfish_fork_choice_passes_supporter_majority E σ h_max T tree cur
      votes support s hsub hmajority hAB (hpath hAB)
  · rw [Protocol.goldfish_fork_choice]
    exact Block.preceq_trans hBA
      (ghost_preceq A tree (Protocol.goldfish_score E T votes support s)
        (Protocol.goldfish_eligible E σ h_max T cur votes support s))


/-- The confirmation-to-head bridge with the minimal anchor invariant:
compatibility, plus candidate-tree membership only in the branch where the
anchor is above the confirmed block. -/
theorem goldfish_fork_choice_captures_of_confirmation
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : Protocol.voters_count E sourceLate s <
      2 * Protocol.goldfish_score E sourceTree sourceVotes sourceVotes s B)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s) := by
  exact goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub (confirmation_adoption hN hT heligible).2
    hcompatible hpath


end Protocol
end DecoupledConsensusModel

end
