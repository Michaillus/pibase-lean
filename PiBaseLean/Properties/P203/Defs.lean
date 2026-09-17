module

public import Mathlib.Topology.Order
public import PiBaseLean.Bundled.Defs

@[expose] public section

namespace PiBase

/- 203. Almost discrete -/
@[mk_iff]
class AlmostDiscreteSpace (X : Type*) [TopologicalSpace X] : Prop where
  ex_point : ∃ p : X, ∀ x : X, x ≠ p ↔ IsOpen {x}

end PiBase
