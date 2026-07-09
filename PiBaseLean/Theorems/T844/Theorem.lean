module

public import Mathlib
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.Topology.Constructions
public import PiBaseLean.Properties.Bundled.Basic
public import PiBaseLean.Properties.P203.Defs
public import PiBaseLean.Properties.P219.Defs
public import PiBaseLean.Properties.P78.Defs

@[expose] public section

universe u

open Topology Set Function Cardinal

namespace PiBase

/-- Theorem T844: P219 (TorontoSpace) ∧ P203 (AlmostDiscreteSpace) => P78 (Finite) -/
theorem instFiniteOfTorontoSpaceAndAlmostDiscreteSpace (X : Type u)
    [TopologicalSpace X] [h1 : TorontoSpace X] [h2 : AlmostDiscreteSpace X] : Finite X := by
  by_contra h
  rw [not_finite_iff_infinite] at h
  obtain ⟨p, hp⟩ := h2.ex_point
  /- have h3 : #X = #(X \ {p}) := by sorry -/
  have h3 : #{ x : X // x ≠ p } = #X  := by
    /- rw [← mk_add_one_eq] -/
    sorry
  have h4 := h1.toronto h3
  have h5 : DiscreteTopology { x : X // x ≠ p } := by
    sorry
  obtain ⟨f⟩ := h4
  simp at f h5
  have h6 := @Homeomorph.discreteTopology _ _ _ _ h5 f
  have hx_open := isOpen_discrete {p}
  have h7 := (hp p).mpr hx_open
  exact (ne_self_iff_false p).mp h7

end PiBase

namespace PiBase.Formal

theorem T844 : P219 ⊓ P203 ≤ P78 := fun X _ ⟨h1, h2⟩ ↦ @instFiniteOfTorontoSpaceAndAlmostDiscreteSpace X _ h1 h2

end PiBase.Formal
