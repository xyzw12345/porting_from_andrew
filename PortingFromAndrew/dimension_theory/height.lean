import Mathlib

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The height of a prime ideal is defined as the supremum of the lengths of strictly decreasing
chains of prime ideals below it. -/
noncomputable def Ideal.primeHeight [I.IsPrime] : WithTop ℕ :=
  Set.chainHeight {J : Ideal R | J.IsPrime ∧ J < I}

/-- The height of an ideal is defined as the infimum of the heights of minimal prime ideals
containing it. -/
noncomputable def Ideal.height : WithTop ℕ :=
  ⨅ J ∈ I.minimalPrimes, by
    have hJ : J ∈ I.minimalPrimes := by assumption
    have hJp : J.IsPrime := by sorry -- This should be provable but we'll skip it for now
    exact Ideal.primeHeight J

/-- For a prime ideal, its height equals its prime height. -/
lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  unfold height primeHeight
  rw [Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- An ideal has finite height if it is either the top ideal or its height is not top. -/
class Ideal.FiniteHeight : Prop where
  eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤

lemma Ideal.finiteHeight_iff_lt {I : Ideal R} :
  Ideal.FiniteHeight I ↔ I = ⊤ ∨ I.height < ⊤ := by
  constructor
  · intro h
    cases h.eq_top_or_height_ne_top with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (lt_of_le_of_ne le_top h)
  · intro h
    constructor
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (ne_top_of_lt h)

lemma Ideal.height_ne_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height ≠ ⊤ :=
  (h.eq_top_or_height_ne_top).resolve_left hI

lemma Ideal.height_lt_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height < ⊤ := by
  exact lt_of_le_of_ne le_top (Ideal.height_ne_top hI)

lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top (by exact h.ne_top)

lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top (by exact h.ne_top)

-- This lemma might need additional theorems for translation
lemma Ideal.primeHeight_succ [h : I.IsPrime] :
  I.primeHeight + 1 = Set.chainHeight {J : Ideal R | J.IsPrime ∧ J ≤ I} := by
  sorry


lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
  I.primeHeight ≤ J.primeHeight := by
  unfold primeHeight
  apply Set.chainHeight_mono
  intro x
  simp only [Set.mem_setOf_eq, and_imp]
  intro h1 h2
  exact ⟨h1, h2.trans_le h⟩

lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
  I.primeHeight + 1 ≤ J.primeHeight := by
  rw [primeHeight_succ]
  apply Set.chainHeight_mono
  intro x
  simp only [Set.mem_setOf_eq, and_imp]
  intro h1 h2
  exact ⟨h1, lt_of_le_of_lt h2 h⟩

lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime]
  (h : I < J) [J.FiniteHeight] :
  I.primeHeight < J.primeHeight := by
  have H := Ideal.primeHeight_add_one_le_of_lt h
  cases hJ : J.primeHeight
  · exact False.elim (J.primeHeight_ne_top hJ)
  cases hI : I.primeHeight
  · sorry -- handling top case
  · sorry -- completing proof with natural number arithmetic

lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
  (h : I < J) [I.FiniteHeight] :
  I.height < J.height := by
  rw [Ideal.height_eq_primeHeight I, Ideal.height]
  sorry -- The rest of the proof needs additional helper lemmas

theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    show p ∈ (∅ : Set (Ideal R))
    rw [← e]; exact hp.1
  · intro h
    rw [h]
    sorry
    -- exact minimalPrimes_top

theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  constructor
  · intro h
    have := h.1.1
    sorry
    -- exact absurd (Eq.refl ⊤) (this rfl)
  · intro h
    exact False.elim (Set.not_mem_empty p h)

theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp only [height, minimalPrimes_top]
  sorry

theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [height]
  apply le_iInf
  intro p hp
  -- obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp)
  sorry

theorem withTop.supr_add {ι : Sort u} [Nonempty ι]
    (f : ι → WithTop ℕ) (x : WithTop ℕ) :
    ⨆ i, f i + x = (⨆ i, f i) + x := by
  cases x
  case top =>
    simp only [add_top]
    apply le_antisymm
    · apply ciSup_le
      intro i
      exact le_top
    · simp
  case coe x =>
    have : ↑x ≤ ⨆ i, f i + ↑x := by
      sorry
    sorry

theorem withTop.supr₂_add {ι : Sort u} {p : ι → Prop} (hs : ∃ i, p i)
    (f : ∀ (i : ι), p i → WithTop ℕ) (x : WithTop ℕ) :
    (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x := by
  haveI : Nonempty { i // p i } := ⟨⟨_, hs.choose_spec⟩⟩
  sorry