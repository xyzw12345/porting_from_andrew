import Mathlib

variable {R : Type _} [CommRing R]

open PrimeSpectrum TopologicalSpace Set

/-- Helper function to find maximal elements with respect to a relation -/
def maximals {α : Type _} (r : α → α → Prop) (s : Set α) : Set α :=
  {x ∈ s | ∀ y ∈ s, r x y → r y x}

/-- Given a function f between two types with relations r and s,
if f preserves and reflects the relations on a set t and is injective on t,
then the image of the maximal elements of t under r equals the maximal elements
of the image of t under s. -/
lemma imageMaximals {α β : Type _} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
  (t : Set α)
  (h₁ : ∀ (x y : α), x ∈ t → y ∈ t → (r x y ↔ s (f x) (f y))) : f '' maximals r t = maximals s (f '' t) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact ⟨x, hx.1, rfl⟩
    · rintro y ⟨w, hw, rfl⟩ h
      rw [← h₁ w x hw hx.1]
      exact hx.2 w hw ((h₁ x w hx.1 hw).mpr h)
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    use x
    constructor
    · constructor
      · exact hx
      · intro y hy hy'
        rw [h₁ y x hy hx]
        simp_all only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        --exact h ⟨y, hy, rfl⟩ ((h₁ x y hx hy).mp hy')
    · rfl

/- The zero locus of minimal prime ideals equals the irreducible components
    of the prime spectrum. -/
theorem zeroLocus_minimal_primes :
  (zeroLocus ∘ SetLike.coe) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R) := by
  exact PrimeSpectrum.zeroLocus_minimalPrimes R

/-- The vanishing ideal of the irreducible components equals the minimal primes -/
theorem vanishingIdeal_irreducibleComponents :
  vanishingIdeal '' irreducibleComponents (PrimeSpectrum R) = minimalPrimes R := by
  have h1 := zeroLocus_minimalPrimes R
  have h2 : (zeroLocus ∘ SetLike.coe) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R) := h1
  ext p
  constructor
  · intro h
    obtain ⟨s, hs, hp⟩ := h
    have : s ∈ irreducibleComponents (PrimeSpectrum R) := hs
    rw [← h2] at this
    obtain ⟨q, hq₁, hq₂⟩ := this
    rw [← hp, ← hq₂]
    simp only [Function.comp_apply, vanishingIdeal_zeroLocus_eq_radical]
    rw [Ideal.IsPrime.radical]
    · exact hq₁
    · unfold minimalPrimes Ideal.minimalPrimes Minimal at hq₁
      simp only [bot_le, and_true, mem_setOf_eq] at hq₁
      exact hq₁.1
  · intro h
    use zeroLocus (SetLike.coe p)
    constructor
    · rw [← h2]
      use p
      constructor
      · exact h
      · rfl
    · rw [vanishingIdeal_zeroLocus_eq_radical]
      rw [Ideal.IsPrime.radical]
      unfold minimalPrimes Ideal.minimalPrimes Minimal at h
      simp only [bot_le, and_true, mem_setOf_eq] at h
      exact h.1

theorem minimalPrimes_finite [IsNoetherianRing R] : (minimalPrimes R).Finite := by
  rw [← vanishingIdeal_irreducibleComponents]
  exact Set.Finite.image vanishingIdeal NoetherianSpace.finite_irreducibleComponents

namespace Ideal

theorem minimalPrimes_finite [IsNoetherianRing R] (I : Ideal R) :
  I.minimalPrimes.Finite := by
  rw [minimalPrimes_eq_comap]
  apply Set.Finite.image (comap (Quotient.mk I))
  exact _root_.minimalPrimes_finite

end Ideal
