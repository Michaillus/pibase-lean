module

public import Mathlib
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.Topology.Constructions
public import PiBaseLean.Bundled.Basic
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
  by_contra! h3
  obtain ⟨p, hp⟩ := h2.ex_point
  have h_card : #{ x : X // x ≠ p } = #X  := by
    have h : #{ x : X // x ≠ p } = #(Set.univ \ {p} : Set X) := by
      congr
      simp
    rw [h]
    have h_Xinf := @Set.infinite_univ X h3
    have h_pfin : Set.Finite {p} := finite_singleton p
    simp [Cardinal.mk_sdiff_eq_left_of_finite h_Xinf h_pfin, mk_univ]
  have ⟨f⟩ := h1.toronto h_card
  have h5 : DiscreteTopology { x : X // x ≠ p } := by
    rw [discreteTopology_iff_isOpen_singleton]
    choose a
    rw [isOpen_induced_iff]
    use {a.val}
    constructor
    · exact (hp a.val).mp a.property
    · rw [← Set.image_singleton]
      exact Subtype.val_injective.preimage_image ({a} : Set {x // x ≠ p})
  have h6 := @Homeomorph.discreteTopology _ _ _ _ h5 f
  have hx_open := isOpen_discrete {p}
  have h7 := (hp p).mpr hx_open
  exact (ne_self_iff_false p).mp h7

end PiBase

namespace PiBase.Formal

theorem T844 : P219 ⊓ P203 ≤ P78 := fun X _ ⟨h1, h2⟩ ↦ @instFiniteOfTorontoSpaceAndAlmostDiscreteSpace X _ h1 h2

end PiBase.Formal
