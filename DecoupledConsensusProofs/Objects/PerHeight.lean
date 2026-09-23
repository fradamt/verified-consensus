module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Divergence

@[expose] public section

/-!
# L4 — per-height completability, the arithmetic half
(`the design` §9 L4; `the design notes` §5;
PROTOCOL.md#the-complete-protocol)

> At most one target per height can ever reach honest target weight `≥ q − b`:
> honest validators target one block per height (E1), and two such targets need
> `2(q−b) ≤ W−b`, i.e. `b ≥ 2q − W ≥ W/3`.

L4 has two inputs and they separate cleanly. The **honest core** — no honest
validator emits two different targets at one height — is the retired
`AlignedRoundLemmas.honest_no_double_target`, and it comes back with the record
layer; it is carried here as the hypothesis
`Internal.HealingSurface.HonestNoDoubleTarget`. The **arithmetic** is this file, and
it needs nothing but the core, `BelowOneThird`, and the definition of `q`.

**Why this matters beyond L4 itself.** Rev. 4 of `Internal.AlignedRound` deleted
clause (e) on the ground that it is a theorem — namely L4 — and L4 then retired
with the record layer, leaving the predicate one lemma short of its own
rationale (`the design notes` §5). This is the second half of that debt
paid: once the core returns, `perHeightCompletability_of` is the clause.

**The counting, in one line.** The two honest backing sets are disjoint by the
core, so `w(Q) + w(Q′) + b ≤ W`. Each is completable, so `q ≤ w(Q) + b` and
`q ≤ w(Q′) + b`, giving `2q ≤ W + b`, hence `6q ≤ 3W + 3b < 4W`. And
`q = ⌈2W/3⌉` gives `4W ≤ 6q`. Nothing here counts committee members, asks who
proposed, or reads a store: "adversarial double-signing does not help, only
honest weight counts" is the statement that the adversary's whole weight `b`
already sits on **both** sides of the comparison.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `q = ⌈2W/3⌉` reflected as `2W ≤ 3q` (PROTOCOL.md#the-complete-protocol).

The one place in this file that unfolds `(2W+2)/3`, in the shape
`Weights.isQuorum_iff_three_mul_weight` uses for the other direction. -/
theorem two_mul_W_le_three_mul_q (E : Env V) : 2 * E.W ≤ 3 * E.q := by
  unfold Env.q Env.W Electorate.finalityThreshold Electorate.totalWeight
  omega

/-- **L4, per-height completability** (`the design` §9 L4).

Two targets at one height cannot both be completable from honest weight: the
honest core makes their backing sets disjoint, and the fault bound closes the
count. -/
theorem perHeightCompletability_of (S : Setup V) {ρ : Run V}
    (hfb : BelowOneThird S ρ.honest)
    (hcore : Internal.HealingSurface.HonestNoDoubleTarget S ρ) :
    Internal.HealingSurface.PerHeightCompletability S ρ := by
  rintro h T T' ⟨Q, hQhon, hQw, hQem⟩ ⟨Q', hQ'hon, hQ'w, hQ'em⟩
  by_contra hne
  -- Disjointness: a validator in both would have emitted two targets at `h`.
  have hsub : Q ∩ Q' ⊆ (∅ : Finset V) := by
    intro v hv
    obtain ⟨hvQ, hvQ'⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, t, hemit, hmem⟩ := hQem v hvQ
    obtain ⟨a', t', hemit', hmem'⟩ := hQ'em v hvQ'
    exact absurd (hcore v (hQhon hvQ) a a' t t' hemit hemit' h T T' hmem hmem') hne
  have hinter : S.E.electorate.weightOf (Q ∩ Q') ≤ 0 :=
    le_trans (S.E.electorate.weightOf_mono hsub) (le_of_eq Finset.sum_empty)
  have hie := S.E.electorate.weight_inter_add_weight_union Q Q'
  -- Both sets sit inside the honest weight, which is `W − b`.
  have hunion : S.E.electorate.weightOf (Q ∪ Q') ≤
      S.E.electorate.weightOf ρ.honest :=
    S.E.electorate.weightOf_mono (Finset.union_subset hQhon hQ'hon)
  have hcompl := S.E.electorate.weightOf_add_weightOf_sdiff ρ.honest
  have hq := two_mul_W_le_three_mul_q S.E
  unfold BelowOneThird at hfb
  unfold Env.W at hfb hq
  omega

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
