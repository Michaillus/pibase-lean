module

public import Mathlib
public import PiBaseLean.Bundled.Basic
public import PiBaseLean.Properties.P129.Defs
public import PiBaseLean.Properties.P219.Defs

@[expose] public section

universe u

open Topology Set Function

namespace PiBase

instance {p : X → Prop} [TopologicalSpace X] [IndiscreteTopology X] :
    IndiscreteTopology (Subtype p) := by
  refine ⟨top_unique fun s h ↦ ?_⟩
  have ⟨t, ht1, ht2⟩ := isOpen_induced_iff.mp h
  rcases (IndiscreteTopology.isOpen_iff t).mp ht1
  <;> simp_all [Eq.comm]

/-- Theorem T814: P129 (IndiscreteTopology) => P219 (TorontoSpace) -/
theorem instTorontoSpaceOfIndiscreteTopology (X : Type u)
    [TopologicalSpace X] [h : IndiscreteTopology X] :
    TorontoSpace X := by
  refine ⟨fun Y h1 ↦ ⟨?_, ?_, ?_⟩⟩
  · exact (Cardinal.eq.mp h1).some
  · exact continuous_of_indiscreteTopology
  · exact continuous_of_indiscreteTopology

end PiBase

namespace PiBase.Formal

theorem T814 : P129 ≤ P219 := fun X _ ↦ @instTorontoSpaceOfIndiscreteTopology X _

end PiBase.Formal
