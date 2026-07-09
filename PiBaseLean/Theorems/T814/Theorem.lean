module

public import Mathlib
public import PiBaseLean.Properties.Bundled.Basic
public import PiBaseLean.Properties.P129.Defs
public import PiBaseLean.Properties.P219.Defs

@[expose] public section

universe u

open Topology Set Function

namespace PiBase

/-- Theorem T817: P129 (IndiscreteTopology) => P219 (TorontoSpace) -/
theorem instTorontoSpaceOfIndiscreteTopology (X : Type u)
    [TopologicalSpace X] [h : IndiscreteTopology X] :
    TorontoSpace X := by
  refine ⟨fun Y h ↦ ⟨Cardinal.eq.mp h |>.some, ?_, ?_⟩⟩
  exact continuous_of_indiscreteTopology

  have h1 : IndiscreteTopology Y := by
    refine ⟨?_⟩
    sorry

  exact continuous_of_indiscreteTopology
  done

end PiBase

namespace PiBase.Formal

theorem T814 : P129 ≤ P219 := fun X _ ↦ @instTorontoSpaceOfIndiscreteTopology X _

end PiBase.Formal
