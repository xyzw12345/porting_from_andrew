import Mathlib

variable (R M A : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Ring A] [Algebra R A]

/-- The support of a module, consisting of prime ideals where the localization is nontrivial -/
def Module.support' [Module R M] : Set (Ideal R) := { I | ∃ h : I.IsPrime, Nontrivial (LocalizedModule I.primeCompl M) }

/-- Characterization of when a localized module is nontrivial -/
theorem localizedModuleNontrivalIff (S : Submonoid R) : Nontrivial (LocalizedModule S M) ↔ ∃ x : M, Disjoint (S : Set R) ((Submodule.span R {x}).annihilator) := by sorry

theorem localizedModuleNontrival (M : Submonoid R) : Nontrivial (LocalizedModule M A) ↔ Disjoint (M : Set R) (RingHom.ker (algebraMap R A)) := by sorry

theorem Module.support_eq_of_algebra : Module.support' R A = { I | RingHom.ker (algebraMap R A) ≤ I ∧ I.IsPrime } := by sorry

/-- Membership in the support is equivalent to nontriviality of localization -/
theorem Module.memSupportIff {I : Ideal R} [hI : I.IsPrime] :
    I ∈ Module.support' R M ↔ Nontrivial (LocalizedModule I.primeCompl M) := by
  simp [Module.support']
  constructor
  · intro h
    sorry
    --exact h.some_spec
  · intro h
    exact ⟨hI, h⟩

/-- General characterization of support membership in terms of primeness and annihilators -/
theorem Module.memSupportIffExists {I : Ideal R} :
    I ∈ Module.support' R M ↔ I.IsPrime ∧ ∃ x : M, (Submodule.span R {x}).annihilator ≤ I := by
  constructor
  · intro h
    have ⟨hprime, h'⟩ := h
    exact ⟨hprime, by sorry⟩
      --rw [memSupportIff] at h'
      --exact h'⟩
  · intro ⟨hprime, h⟩
    exact ⟨hprime, by sorry⟩
      --rw [memSupportIff]
      --exact h⟩

theorem Module.supportEqExists :
    Module.support' R M = { I | I.IsPrime ∧ ∃ x : M, (Submodule.span R {x}).annihilator ≤ I } := by
  ext I
  sorry
  --exact Module.memSupportIffExists

theorem Module.existsAnnihilatorLeOfMemSupport {I : Ideal R} (h : I ∈ Module.support' R M) :
    ∃ x : M, (Submodule.span R {x}).annihilator ≤ I := by sorry
  -- exact (Module.memSupportIffExists.mp h).2

theorem Module.memSupportOfLe {I J : Ideal R} (h : I ≤ J) (hI : I ∈ Module.support' R M)
    [hJ : J.IsPrime] : J ∈ Module.support' R M := by
  rw [Module.memSupportIffExists] at hI ⊢
  exact ⟨hJ, sorry⟩ --exists_imp_exists (λ _ => le_trans) hI.2⟩

theorem Module.annihilatorLeOfMemSupport {I : Ideal R} (h : I ∈ Module.support' R M) :
    (⊤ : Submodule R M).annihilator ≤ I := by sorry
  --exact (Submodule.annihilator_mono le_top).trans
    --(Module.existsAnnihilatorLeOfMemSupport h).some_spec

/-- For finitely generated modules, membership in the support is equivalent to containing
    the annihilator of the top submodule -/
theorem Module.memSupportIffAnnihilatorLeOfFg {I : Ideal R} [I.IsPrime]
    [Module.Finite R M] :
    I ∈ Module.support' R M ↔ (⊤ : Submodule R M).annihilator ≤ I := by
  constructor
  · intro h
    rcases h with ⟨_, x, hx⟩
    sorry
    --exact Submodule.annihilator_mono le_top ▸ hx
  · intro h
    constructor
    · sorry --exact inferInstance
    · sorry
      --rcases Module.Finite.exists_generator M with ⟨S, hS⟩
      --se S.1
      --exact Submodule.annihilator_mono (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hS)) ▸ h

/-- For finitely generated modules, the support equals the set of prime ideals containing
    the annihilator -/
theorem Module.supportEqOfFg [hM : Module.Finite R M] :
    Module.support' R M = { I | (⊤ : Submodule R M).annihilator ≤ I ∧ I.IsPrime } := by
  ext I
  constructor
  · intro h
    sorry --exact ⟨(memSupportIffAnnihilatorLeOfFg R M).mp h, h.1⟩
  · intro h
    haveI : I.IsPrime := h.2
    exact (memSupportIffAnnihilatorLeOfFg R M).mpr h.1

/-- The support is nonempty if and only if the module is nontrivial -/
theorem Module.supportNonemptyIff :
    (Module.support' R M).Nonempty ↔ Nontrivial M := by
  constructor
  · rintro ⟨I, hI⟩
    rcases hI with ⟨_, x, hx⟩
    sorry --exact ⟨x, λ h => hx (Submodule.mem_annihilator.mpr (λ _ => h ▸ zero_smul _ _))⟩
  · intro h
    sorry --rcases exists_ne_zero M with ⟨x, hx⟩
    --obtain ⟨P, hP⟩ := Ideal.exists_le_maximal _
      --((Submodule.span R {x}).annihilator.ne_top_iff_one.mpr
        --(λ h => hx (one_smul R x ▸ h)))
    --exact ⟨P, ⟨inferInstance, x, hP⟩⟩

/-- The support of a module is empty if and only if the module is subsingleton -/
theorem Module.supportEqEmptyIff' :
    { I : Ideal R | ∃ h : I.IsPrime, Nontrivial (LocalizedModule I.primeCompl M) } = ∅ ↔
    Subsingleton M := by
  rw [Set.eq_empty_iff_forall_not_mem]
  constructor
  · intro h
    sorry
    /-
    rw [← notNontrivalIffSubsingleton]
    intro hN
    have := Module.supportNonemptyIff.mpr hN
    rcases this with ⟨I, hI⟩
    exact h I hI
    -/
  · intro h I hI
    sorry
    /-
    have := notNontrivalIffSubsingleton.mpr h
    have := Module.supportNonemptyIff.mp ⟨I, hI⟩
    contradiction-/

/-- The support of a nontrivial module is nonempty -/
theorem Module.supportNonempty' [h : Nontrivial M] :
    (Module.support' R M).Nonempty := by sorry
  --exact Module.supportNonemptyIff.mpr h

/-- The support of a subsingleton module is empty -/
theorem Module.supportEqEmpty' [h : Subsingleton M] :
    Module.support' R M = ∅ := Module.supportEqEmptyIff' R M |>.mpr h

/-- A ring element `r` acts locally nilpotently on a module `M` if for every element `m` of `M`,
    there exists some power of `r` that annihilates `m`. -/
def Module.IsLocallyNilpotent (r : R) : Prop :=
  ∀ m : M, ∃ n : ℕ, r ^ n • m = 0

/-- Three-way equivalence between subsingleton of localized module,
    locally nilpotent action, and membership in infimum of support -/
theorem Module.memInfSupportTfae (x : R) :
    (Subsingleton (LocalizedModule (Submonoid.powers x) M) ↔
      (Module.IsLocallyNilpotent R M x)) ∧
    (Module.IsLocallyNilpotent R M x ↔ ∀ (I : Ideal R), I ∈ Module.support' R M → x ∈ I) := by
  constructor
  · constructor
    · intro h m
      -- From subsingleton to locally nilpotent
      sorry /- have := localizedModuleNontrivalIff (Submonoid.powers x) M
      rw [← not_nontrivial_iff_subsingleton] at h
      rw [this] at h
      push_neg at h
      obtain ⟨n, hn⟩ := h m
      exact ⟨n, hn⟩ -/
    · intro h
      -- From locally nilpotent to subsingleton
      rw [← not_nontrivial_iff_subsingleton, localizedModuleNontrivalIff]
      push_neg
      sorry --exact h

  · sorry

/-- Membership in the infimum of support is equivalent to locally nilpotent action -/
theorem Module.memInfSupportIffLocallyNilpotent {x : R} :
    (∀ (I : Ideal R), ∃ h : I.IsPrime, Nontrivial (LocalizedModule I.primeCompl M) → x ∈ I) ↔
    Module.IsLocallyNilpotent R M x := by sorry

/-- For finitely generated modules, the infimum of the support equals the radical of the annihilator -/
theorem Module.InfSupportEqAnnihilatorRadical [h : Module.Finite R M] :
    {x : R | ∀ I : Ideal R, I ∈ Module.support' R M → x ∈ I} =
    (⊤ : Submodule R M).annihilator.radical := by sorry

/-- Characterization of locally nilpotent action in terms of radical membership for finitely generated modules -/
theorem Module.isLocallyNilpotentIffMemRadical [h : Module.Finite R M] (x : R) :
    Module.IsLocallyNilpotent R M x ↔ x ∈ (⊤ : Submodule R M).annihilator.radical := by sorry
  --rw [← Module.memInfSupportIffLocallyNilpotent]
  --rw [Module.InfSupportEqAnnihilatorRadical]

/-- Characterization of locally nilpotent action for algebras -/
theorem Module.isLocallyNilpotentOfAlgebra {x : R} :
    Module.IsLocallyNilpotent R M x ↔ x ∈ (algebraMap R A).ker.radical := by sorry
  --rw [← Module.memInfSupportIffLocallyNilpotent]
  --conv =>
    --rhs
    --rw [← Module.support_eq_of_algebra]
