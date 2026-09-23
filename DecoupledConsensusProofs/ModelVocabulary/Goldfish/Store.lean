module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Objects
public import DecoupledConsensusModel.Protocol.StoreBase
public import DecoupledConsensusInternal.ModelVocabulary.Goldfish.Store
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Fold
public import DecoupledConsensusModel.Protocol.Schedule

@[expose] public section

/-!
# §2.2 Store — `sec:goldfish-store`, `def:store` (PROTOCOL.md `sec:goldfish-store`)

The seven components of `def:store`, the initial store, and the three derived
notions the section states over it: equivocation detection, *resolution*, and
the resolution time `τ`.

Three shapes are forced here.

* The document's single `timestamp[·]`, keyed by "block or vote"
  (PROTOCOL.md `def:store`), becomes two typed maps. Lean has no untyped key.
* `gf_votes[k]` is a *list*, not a `Finset`. `Block.gf_votes` already is one
  (modeling-choices row 17), and `Finset.toList` is noncomputable in Mathlib, so
  a `Finset` pool could not be copied into a proposal at all. The handler's
  duplicate guard (PROTOCOL.md `alg:goldfish-store`, "no rule needs a third
  pool entry") is what keeps the list a set; set-valued reads go through
  `Store.pool`.
* The store binder is `st`. `Σ` is Sigma-type notation in Lean and cannot be a
  binder name.

This is the base of the `extends` chain: §3, §5, §6 and §7 add fields to *this*
structure and never rename one (PROTOCOL.md `sec:substrate`, modeling-choices
row 8).
-/

namespace DecoupledConsensusModel
namespace Protocol

section Resolution

variable {V : Type} [DecidableEq V]

/-- §2.6 "Because `early ⊆ late`…" (PROTOCOL.md `sec:available-confirmation`,
"equivocating in"), at one vote: a vote
resolved before `Γ` was received before `Γ`.

This is what keeps the inclusion true after the τ fold split the two sets onto
different clocks — the numerator tightened, the denominator did not. -/
theorem stampedBefore_of_resolution {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V}
    (h : stampedBefore (resolution_time T tb tv) Γ vote = true) :
    stampedBefore tv Γ vote = true := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time] at h ⊢
  cases hf : Block.find? T vote.head with
  | none => rw [hf] at h; exact absurd h (by simp [occurrenceBefore])
  | some H =>
      rw [hf] at h
      by_cases hslot : H.slot ≤ vote.slot
      · simp [hslot] at h
        exact occurrenceBefore_of_max_left h
      · simp [hslot, occurrenceBefore] at h

/-- §2.2 `τ(vote) < Γ` from the two receipt bounds (PROTOCOL.md
`sec:goldfish-store`, "resolution time").

This is the whole content of the τ fold on the proof side: a `τ` bound is two
receipt bounds, the vote's own and the named block's. The second is **not**
derivable from the document — see the `HeadsResolveIn` conditional. -/
theorem stampedBefore_resolution_of {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V} {H : Block V}
    (hfind : Block.find? T vote.head = some H) (hslot : H.slot ≤ vote.slot)
    (hv : stampedBefore tv Γ vote = true) (hH : stampedBefore tb Γ H = true) :
    stampedBefore (resolution_time T tb tv) Γ vote = true := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time, hfind, hslot] at hv hH ⊢
  exact occurrenceBefore_max hv hH

/-- A vote with a finite resolution time names a block from its own slot or
earlier. The guard is part of `resolution_time`, so this fact does not need an
environmental target-slot premise. -/
theorem head_slot_le_of_resolution_time {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V} {H : Block V}
    (hfind : Block.find? T vote.head = some H)
    (hτ : stampedBefore (resolution_time T tb tv) Γ vote = true) :
    H.slot ≤ vote.slot := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time, hfind] at hτ
  by_contra hslot
  simp [hslot, occurrenceBefore] at hτ

end Resolution

end Protocol
end DecoupledConsensusModel

end
