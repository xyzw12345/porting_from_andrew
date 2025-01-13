import Mathlib

namespace TopologicalSpace

open Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The set of points whose singleton sets are closed. -/
def closedPoints (α : Type*) [TopologicalSpace α] : Set α :=
  { x : α | IsClosed ({x} : Set α) }

/-- Membership in closed points is equivalent to the singleton being closed. -/
lemma memClosedPoints {α : Type*} [TopologicalSpace α] {x : α} :
  x ∈ closedPoints α ↔ IsClosed ({x} : Set α) := Iff.rfl

/-- A space is Jacobson if every closed set is the closure of its intersection with closed points. -/
def isJacobson (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ Z, IsClosed Z → closure (Z ∩ closedPoints α) = Z

/-- Main characterization of Jacobson spaces in terms of locally closed sets -/
theorem isJacobsonIffLocallyClosed {α : Type*} [TopologicalSpace α] :
  isJacobson α ↔ ∀ Z : Set α, Z.Nonempty → IsLocallyClosed Z → (Z ∩ closedPoints α).Nonempty := by
  sorry

/-- A locally closed singleton in a Jacobson space is closed -/
theorem isJacobson.isClosedOfIsLocallyClosed {α : Type*} [TopologicalSpace α]
    (hα : isJacobson α) {x : α} (hx : IsLocallyClosed ({x} : Set α)) :
    IsClosed ({x} : Set α) := by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ := (isJacobsonIffLocallyClosed.mp hα) {x}
    (Set.singleton_nonempty x) hx
  exact hy'

/-- The preimage of closed points under an embedding is contained in the closed points. -/
lemma preimageClosedPointsSubset (f : α → β) (hf : IsEmbedding f) :
  f ⁻¹' (closedPoints β) ⊆ closedPoints α := by
  intro x hx
  simp only [closedPoints, Set.mem_setOf_eq] at *
  convert continuous_iff_isClosed.mp hf.continuous _ hx using 1
  rw [← Set.image_singleton, Set.preimage_image_eq _ hf.injective]

/-- For a closed embedding, the preimage of closed points equals the closed points. -/
lemma IsClosedEmbedding.preimageClosedPoints {f : α → β} (hf : IsClosedEmbedding f) :
  f ⁻¹' (closedPoints β) = closedPoints α := by
  ext x
  simp only [closedPoints, Set.mem_setOf_eq, Set.mem_preimage, ← Set.image_singleton]
  sorry

/-- For an open embedding into a Jacobson space, the preimage of closed points equals the closed points. -/
lemma IsOpenEmbedding.preimageClosedPoints {f : α → β} (hf : IsOpenEmbedding f)
    (hβ : isJacobson β) : f ⁻¹' (closedPoints β) = closedPoints α := by
  apply Set.Subset.antisymm (preimageClosedPointsSubset f hf.isEmbedding)
  intro x hx
  apply hβ.isClosedOfIsLocallyClosed
  rw [← Set.image_singleton]
  sorry
  --exact IsLocallyClosed.image hx hf.continuous hf.isOpen_range

/-- A space is Jacobson if it has an open embedding into a Jacobson space. -/
theorem isJacobson.ofOpenEmbedding {f : α → β} (hα : isJacobson β)
    (hf : IsOpenEmbedding f) : isJacobson α := by sorry
  --have h_pre := hf.preimageClosedPoints hα
  --intro Z hZ

/-- A space is Jacobson if it has a closed embedding into a Jacobson space. -/
theorem isJacobson.ofClosedEmbedding {f : α → β} (hα : isJacobson β)
    (hf : IsClosedEmbedding f) : isJacobson α := by sorry
  --have h_pre := hf.preimageClosedPoints
  --intro Z hZ

/-- If a finite topological space is Jacobson, then it has the discrete topology. -/
theorem isJacobson_discreteOfFinite [Finite α]
    (hα : isJacobson α) : DiscreteTopology α := by sorry

/-- The Jacobson property for topological spaces is characterized by its behavior on open subsets. -/
theorem isJacobson_iffOfSuprEqTop
    {ι : Type*} {U : ι → Opens α} (hU : ⋃ i : ι, (U i : Set α) = ⊤) :
    isJacobson α ↔ ∀ i, isJacobson (U i) := by
  constructor
  · intro h i
    sorry
    --exact h.ofOpenEmbedding (U i).2.openEmbedding_subtypeCoe
  · intro H
    rw [isJacobsonIffLocallyClosed]
    intro Z hZ hZ'
    sorry
    /-
    have h1 : (⋃ i, (U i : Set α)) = univ := by rw [← Opens.coe_supr, hU]; rfl
    have h2 : (⋃ i, Z ∩ U i) = Z := by rw [← inter_Union, h1, inter_univ]
    rw [← h2, nonempty_Union] at hZ
    obtain ⟨i, x, hx, hx'⟩ := hZ
    obtain ⟨y, hy, hy'⟩ := (isJacobsonIffLocallyClosed.mp $ H i) (coe ⁻¹' Z) ⟨⟨x, hx'⟩, hx⟩
      (hZ'.preimage continuous_subtype_coe)
    refine ⟨y, hy, (isClosed_iff_coe_preimage_of_supr_eq_top hU _).mpr fun j => ?_⟩
    by_cases h : (y : α) ∈ U j
    · convert_to IsClosed ({(⟨y, h⟩ : U j)} : Set (U j))
      · ext z; exact @Subtype.coe_inj _ _ z ⟨y, h⟩
      apply (H j).isClosedOfIsLocallyClosed
      convert (hy'.isLocallyClosed.image embeddingSubtypeCoe.toInducing
        (U i).2.openEmbedding_subtypeCoe.openRange.isLocallyClosed).preimage
        continuous_subtype_coe
      rw [image_singleton]
      ext z
      exact (@Subtype.coe_inj _ _ z ⟨y, h⟩).symm
    · convert isClosed_empty
      rw [eq_empty_iff_forall_not_mem]
      rintro z (hz : ↑z = y)
      rw [← hz] at h
      exact h z.2
    -/

end TopologicalSpace
