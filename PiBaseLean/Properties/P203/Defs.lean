module

public import Mathlib.Topology.Order
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 203. Almost discrete -/
@[mk_iff]
class AlmostDiscreteSpace (X : Type*) [TopologicalSpace X] : Prop where
  ex_point : ∃ p : X, ∀ x : X, x ≠ p ↔ IsOpen {x}

end PiBase

namespace PiBase.Formal

def P203 : Property where
  toPred := AlmostDiscreteSpace
  well_defined φ h := by 
    obtain ⟨p, hp⟩ := h
    use φ p
    intro x
    specialize hp (φ.symm x)
    simp [Homeomorph.symm_apply_eq, ← φ.symm.isOpen_image, hp.symm]

end PiBase.Formal
