import Mathlib

theorem Set.eqEmptyOrEqInsert {α : Type*} (s : Set α) :
    s = ∅ ∨ ∃ t : Set α, ∃ x : α, x ∉ t ∧ s = insert x t := by
  match s.eq_empty_or_nonempty with
  | Or.inl h => exact Or.inl h
  | Or.inr ⟨x, hx⟩ =>
    apply Or.inr
    exists s \ {x}, x
    constructor
    · simp
    · simp [Set.insert_eq_of_mem hx]

theorem csuprSubtype {α : Type*} [ConditionallyCompleteLinearOrderBot α]
    {ι : Sort*} {P : ι → Prop} (f : (i : ι) → P i → α) (hf : ∃ X, ∀ i h, f i h ≤ X) :
    (⨆ (i : ι) (h : P i), f i h) = ⨆ (i : Subtype P), f i.val i.prop := by
  obtain ⟨X, hf⟩ := hf
  apply le_antisymm
  · have bounded : BddAbove (Set.range fun (i : Subtype P) => f i.val i.prop) := by
      use X
      rintro _ ⟨x, rfl⟩
      exact hf _ _
    -- exact csSup_le' (fun i ↦ csSup_le' <| fun h ↦ le_csSup bounded ⟨i, h⟩)
    refine ciSup_le' (fun i ↦ ciSup_le' <| fun h ↦ le_ciSup bounded ⟨i, h⟩)
  · exact ciSup_le' fun i =>
    -- { refine csupr_le' (λ i, le_trans _ (le_csupr _ i)),
    -- refine le_trans _ (le_csupr _ i.prop),
    -- { exact rfl.le },
    -- { use X, rintro _ ⟨x, rfl⟩, exact hf _ _ },
    -- { use X, rintro _ ⟨x, rfl⟩, exact csupr_le' (hf x) } }

    -- le_trans (le_csSup _ i.prop)
    --          (le_csSup (fun j => ⨆ h : P j, f j h) i.val)
    sorry

theorem cardinal_le_of_add_one_le_add_one {α β : Cardinal} (h : α + 1 ≤ β + 1) : α ≤ β := by
  exact (Cardinal.add_one_le_add_one_iff).mp h

lemma add_one_le_dim_iff_exists_submodule_rank_eq {R : Type*} {M : Type*} [Field R]
  [AddCommGroup M] [Module R M] {c : Cardinal} :
  c + 1 ≤ Module.rank R M ↔ ∃ p : Submodule R M, p ≠ ⊤ ∧ Module.rank R p = c := by
  rw [le_rank_iff_exists_linearIndependent]
  constructor
  · rintro ⟨s, e, h⟩
    obtain ⟨x, hx⟩ := Cardinal.mk_ne_zero_iff.mp (show Cardinal.mk s ≠ 0 from by simp [e])
    use Submodule.span R (s \ {x})
    constructor
    · intro e
      apply h.not_mem_span_image
        (Set.not_mem_compl_iff.mpr (Set.mem_singleton (⟨x, hx⟩ : s)))
      simp [Set.compl_eq_univ_diff, Set.image_diff Subtype.coe_injective, e]
    · have : x ∉ s \ {x} := fun e => e.2 rfl
      have := Cardinal.mk_insert this
      sorry  -- Need to handle cardinal arithmetic
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, x ∉ p := by
      revert hp
      contrapose!
      rw [eq_top_iff]
      exact fun H x _ => H x
    obtain ⟨b, hbsub, hb⟩ := exists_linearIndependent R (p : Set M)
    sorry -- Need to handle the linear independence extension

lemma rankSuprNeTopAddOne {R : Type*} {M : Type*} [Field R] [AddCommGroup M] [Module R M] :
  (⨆ (p : Submodule R M) (h : p ≠ ⊤), Module.rank R p + 1) = Module.rank R M := by
  rw [csuprSubtype]
  · apply le_antisymm
    · -- First direction
      sorry
    · by_cases h : Module.rank R M = 0
      · rw [h]
        exact zero_le _
      · have hpos : 1 ≤ Module.rank R M := Cardinal.one_le_iff_ne_zero.mpr h
        have : BddAbove (Set.range fun p : {x : Submodule R M // x ≠ ⊤} => Module.rank R p + 1) := by
          use Module.rank R M + 1
          rintro _ ⟨a, rfl⟩
          exact add_le_add (Submodule.rank_le _) rfl.le
        -- Rest of the proof
        sorry
  · use Module.rank R M + 1
    intro _ _
    exact add_le_add (Submodule.rank_le _) rfl.le
