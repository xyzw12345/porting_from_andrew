import Mathlib
import PortingFromAndrew.Jacobson_space

open Ideal PrimeSpectrum TopologicalSpace' Set

/-- If A is a Jacobson ring and B is a finite type A-algebra, then B is also a Jacobson ring -/
theorem IsJacobsonRing.of_finiteType {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] (h1 : IsJacobsonRing A) (h2 : Algebra.FiniteType A B) : IsJacobsonRing B := by
  obtain ⟨ι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial.mp h2
  exact @isJacobsonRing_of_finiteType A B _ _ _ h1 h2

/-- If A is Jacobson and B is a finitely generated A-algebra via a ring homomorphism f,
    then B is Jacobson. -/
lemma isJacobsonOfRingHomFiniteType {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) [h : IsJacobsonRing A] (H : RingHom.FiniteType f) : IsJacobsonRing B := by
  letI : Algebra A B := f.toAlgebra
  have hft : Algebra.FiniteType A B := by
    exact H
  exact IsJacobsonRing.of_finiteType h H

/-- If R is Jacobson, S is a field, and S is a finitely generated and integral R-algebra,
    then S is finite as an R-module. -/
lemma finiteOfFiniteTypeOfIsIntegral (R S : Type*) [CommRing R] [Field S]
    [h : IsJacobsonRing R] [Algebra R S] [h₁ : Algebra.FiniteType R S] [h₂ : Algebra.IsIntegral R S] :
    Module.Finite R S := Algebra.IsIntegral.finite

/-- If R is Jacobson, S is a field, and S is a finitely generated R-algebra,
    then S is finite as an R-module. -/
lemma finiteOfFiniteTypeOfIsJacobsonOfField (R S : Type*) [CommRing R] [Field S]
    [h : IsJacobsonRing R] [Algebra R S] [H : Algebra.FiniteType R S] : Module.Finite R S := by
  obtain ⟨ι, x, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp H
  have integral_comp_c := @MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing R _ _ ι _ S _ f hf
  have algebra_integral : Algebra.IsIntegral R S := by
    sorry
    --apply RingHom.IsIntegral.to_Algebra.IsIntegral
    --exact integral_comp_c
  exact finiteOfFiniteTypeOfIsIntegral R S

/-- If R is a Jacobson ring, then its prime spectrum is a Jacobson space -/
theorem isJacobsonOfIsJacobson (R : Type*) [CommRing R] [IsJacobsonRing R] :
    isJacobson (PrimeSpectrum R) := by
  sorry

/-- The Jacobson radical of an ideal is radical -/
lemma Ideal.isRadicalJacobson {R : Type*} [CommRing R] (I : Ideal R) :
    I.jacobson.IsRadical := isRadical_of_eq_jacobson jacobson_idem

/-- A ring R is Jacobson if and only if its prime spectrum is a Jacobson space -/
theorem isJacobson_iff_isJacobson {R : Type*} [CommRing R] :
    IsJacobsonRing R ↔ isJacobson (PrimeSpectrum R) := by
  constructor
  · intro h
    exact isJacobsonOfIsJacobson R
  · intro H
    constructor
    intro I hI
    apply le_antisymm _ le_jacobson
    · sorry
      /-rw [← Ideal.isRadicalJacobson I]
      rw [← hI.radical]
      simp only [← vanishingIdeal_zeroLocus_eq_radical]
      apply vanishingIdeal_anti_mono
      rw [← H _ (isClosed_zeroLocus I)]
      rw [(isClosed_zeroLocus _).closure_subset_iff]
      intro x hx
      exact iInf_le ⟨hx.1, (isClosed_singleton_iff_isMaximal _).mp hx.2⟩-/
