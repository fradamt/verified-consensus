module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! Internal grade observations. Not part of the final review surface. -/

namespace DecoupledConsensusModel
namespace Internal.HealingSurface

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The raw core view at the actual named strict action-time read.
This is a data projection, not a completed grade or prepared-tick grade read.
The saved cache and the cache prepared inside NamedNode.tick are separate
observations; neither is reconstructed from this store. -/
def healStoreAt (S : Setup V) (ρ : Run V) (v : V) (r : Round) : Protocol.HealingStore V :=
  (ρ.storeBeforeTime S v (S.a r)).core.toHealing

/-- The retained raw input view at `a_r⁻`. This alone is not the saved
G2/G1/G0 result of the named phase runtime. -/
def gradeViewAt (S : Setup V) (ρ : Run V) (v : V) (r : Round) : GradeView V :=
  (healStoreAt S ρ v r).gradeView

end Internal.HealingSurface
end DecoupledConsensusModel

end
