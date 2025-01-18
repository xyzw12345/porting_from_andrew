import Mathlib

universe u

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

/-- The Krull dimension of a commutative ring, defined as the supremum of lengths of chains of prime ideals -/
noncomputable def krullDimension (R : Type u) [CommRing R] : WithTop ℕ :=
  ⨆ (c : Set (Ideal R)) (h : IsChain (· ≤ ·) c) (h' : ∀ I ∈ c, I.IsPrime), ENat.card c

/-- A ring has finite Krull dimension if its Krull dimension is not ⊤ -/
class FiniteKrullDimensional (R : Type u) [CommRing R] : Prop where
  krullDimensionNeTop : krullDimension R ≠ ⊤

variable {R : Type u} [CommRing R]

lemma krullDimensionNeTop [h : FiniteKrullDimensional R] :
  krullDimension R ≠ ⊤ :=
h.krullDimensionNeTop

lemma krullDimensionLtTop [FiniteKrullDimensional R] :
  krullDimension R < ⊤ := by
  exact Ne.lt_top (krullDimensionNeTop)

lemma finiteKrullDimensionalIffLt :
  FiniteKrullDimensional R ↔ krullDimension R < ⊤ := by
  constructor
  · intro h
    exact krullDimensionLtTop
  · intro h
    exact ⟨ne_top_of_lt h⟩

lemma krullDimensionOfSubsingleton [Subsingleton R] :
  krullDimension R = 0 := by
  sorry

instance (priority := 100) finiteKrullDimensionalOfSubsingleton [Subsingleton R] :
  FiniteKrullDimensional R := by
  rw [finiteKrullDimensionalIffLt, krullDimensionOfSubsingleton]
  exact WithTop.top_pos

lemma Ideal.primeHeightLeKrullDimension {I : Ideal R} [I.IsPrime] :
    I.height ≤ krullDimension R := by
  sorry  -- The original uses le_supr₂ which needs to be adapted

instance Ideal.finiteHeightOfFiniteDimensional {I : Ideal R} [FiniteKrullDimensional R] (priority := 900):
    Ideal.FiniteHeight I := by
  rw [Ideal.finiteHeight_iff_lt, or_iff_not_imp_left]
  intro e
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I e
  refine' (Ideal.height_mono hM').trans_lt _
  refine' (lt_of_le_of_lt _ (krullDimensionLtTop (R := R)))
  apply M.primeHeightLeKrullDimension

theorem krullDimensionSucc [Nontrivial R] :
    krullDimension R + 1 = Set.chainHeight {I : Ideal R | I.IsPrime} := by
  have h : ∃ I : Ideal R, I.IsPrime := by
    -- We know such an ideal exists in any nontrivial ring
    sorry
  sorry

/-- If J has finite height and I ≤ J, then I has finite height -/
lemma Ideal.finiteHeightOfLe {R : Type u} [CommRing R] {I J : Ideal R}
  (e : I ≤ J) (hJ : J ≠ ⊤) [FiniteHeight J] :
  FiniteHeight I where
  eq_top_or_height_ne_top := Or.inr <| by
    rw [← lt_top_iff_ne_top]
    exact (height_mono e).trans_lt (height_lt_top hJ)

/-- If J is a prime ideal containing I, and its height is less than or equal to the height of I,
then J is a minimal prime over I -/
lemma Ideal.memMinimalPrimesOfHeightEq {R : Type u} [CommRing R] {I J : Ideal R}
  (e : I ≤ J) [J.IsPrime] [hJ : FiniteHeight J] (e' : height J ≤ height I) :
  J ∈ I.minimalPrimes := by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert h₁
  sorry
  -- refine eq_of_le_of_not_lt h₂ ?_
  -- intro h₃
  -- have := h₁.1.1
  -- have := finiteHeightOfLe h₂ (by exact IsPrime.ne_top)
  -- exact lt_irrefl _
  --   ((height_strict_mono_of_is_prime h₃).trans_le (e'.trans $ height_mono h₁.1.2))

/-- A prime ideal has height zero if and only if it is minimal -/
lemma Ideal.primeHeightEqZeroIff {R : Type u} [CommRing R] {I : Ideal R} [I.IsPrime] :
  primeHeight I = 0 ↔ I ∈ minimalPrimes R := by sorry
  -- rw [primeHeight, Set.chain_height_eq_zero_iff]
  -- constructor
  -- · intro e
  --   exact ⟨⟨inferInstance, bot_le⟩, fun J hJ e' => (eq_of_le_of_not_lt e' ?_).symm.le⟩
  --   intro e''
  --   show J ∈ (∅ : Set (Ideal R))
  --   rw [← e]
  --   exact ⟨hJ.1, e''⟩
  -- · intro hI
  --   ext J
  --   suffices : J.IsPrime → ¬J < I
  --   · simpa
  --   intros hJ e
  --   exact not_le_of_lt e (hI.2 ⟨hJ, bot_le⟩ e.le)
