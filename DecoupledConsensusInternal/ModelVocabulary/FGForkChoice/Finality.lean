module
public import DecoupledConsensusModel

@[expose] public section

/-!
# §5.1 Stored states and finality updates (PROTOCOL.md `sec:fg-fork-choice`)

The store map `Σ.σ[·]`, the four finality fields, the three derived sets, and
the in-place mutator that maintains them.

Four shapes are forced here.

* **`Σ.σ[·]` is a total map** defaulting to the initial chain state of
  `def:chain-state` (modeling-choices row 3). The document writes `σ[·]` only in
  `on_block`, so it is defined exactly on `Σ.T` and never initialized at
  genesis (F5.3, F5.4); `on_block` on a child of genesis nevertheless reads
  `Σ.σ[B.parent]` (PROTOCOL.md `alg:fg-store`), and the initial state is the only
  value consistent with the document.
* **`update_finality` mutates sequentially.** Its three statements execute in
  order and each reads the results of the previous one: the viability test uses
  the *new* `h_max` and the *old* `F`, the `σ.F ⪯ Σ.J` test uses the
  possibly-just-updated `Σ.J`, and the final recomputation uses the *new* `F`
  (F5.2, modeling-choices row 5). Each `let` below is one of the document's
  statements, and the next one reads the store the previous one produced — a
  pre-call snapshot would be a different protocol.
* **`h_max` is monotone.** The live document says it only grows, and the former
  recomputation after `F` advances is gone. The finalized-ancestor admission
  rule makes each block that raises the maximum live when it is admitted.
* **The derived sets are pure functions of plain data.** `T_F` and `V` are
  `Σ`-shaped in the document; each has a pure core over `(F, T)` or
  `(σ, h_max, live)` plus a thin store reader, so §6 and §7 feed their own
  fields to the same rules (conventions: "pure core, thin stores"). Nothing is
  cached: "the store does not cache … a live tree, a viable tree, or a filtered
  tree: each is derived when used" (PROTOCOL.md `sec:complete-store`,
  "derived when used").

  There were **three**. `E_F(Σ)` — the processed finality evidence — is gone,
  with the tex display it transcribed (baseline `a807de9`; doc-feedback item 21,
  their 6b). It had no reader in the model and no reader in the document, and
  the model's own note said so before the tex caught up: "nothing reads it; the
  tex may want to drop the display". Only the unused preamble macro survives
  doc-side. It was also this file's one `Finset.image`, hence its one
  `Classical.choice` term, so the deletion is a small dividend as well as a
  transcription fix.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

namespace FGStore

variable {V : Type} [DecidableEq V]

end FGStore

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §5.2 `viable_tree(Σ)` read off the store. Spelled `V_tree`
because `V` is the validator *type* in every Lean file of this model. -/
def V_tree (st : FGStore V) : Finset (Block V) :=
  viable_tree st.σ st.F st.h_max st.T

end Protocol
end DecoupledConsensusModel

end
