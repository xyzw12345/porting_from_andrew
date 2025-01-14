import Mathlib

theorem Set.eq_empty_or_eq_insert {α : Type*} (s : Set α) :
    s = ∅ ∨ ∃ t : Set α, ∃ x : α, x ∉ t ∧ s = insert x t := by
  match s.eq_empty_or_nonempty with
  | Or.inl h => exact Or.inl h
  | Or.inr ⟨x, hx⟩ =>
    apply Or.inr
    exists s \ {x}, x
    constructor
    · simp
    · simp [Set.insert_eq_of_mem hx]

theorem ciSup_subtype''' {α : Type*} [ConditionallyCompleteLinearOrderBot α]
    {ι : Sort*} {P : ι → Prop} (f : (i : ι) → P i → α) (hf : ∃ X, ∀ i h, f i h ≤ X) :
    (⨆ (i : ι) (h : P i), f i h) = ⨆ (i : Subtype P), f i.val i.prop := by
  obtain ⟨X, hf⟩ := hf
  apply le_antisymm
  · have bounded : BddAbove (Set.range fun (i : Subtype P) => f i.val i.prop) :=
      ⟨X, by rintro _ ⟨i, rfl⟩; exact hf _ _⟩
    refine ciSup_le' (fun i ↦ ciSup_le' <| fun h ↦ le_ciSup bounded ⟨i, h⟩)
  · refine ciSup_le' fun i ↦ ?_
    refine le_trans ?_ (le_ciSup ⟨X, ?_⟩ i.val)
    · refine (le_ciSup ?_ i.prop)
      · use X; rintro _ ⟨x, rfl⟩; exact hf _ _
    · rintro _ ⟨x, rfl⟩; refine ciSup_le' (fun i ↦ hf _ _)

/-- For any cardinal α, there exists a cardinal β such that β + 1 = α if and only if α is not zero. -/
theorem cardinal_exists_add_one_eq_iff {α : Cardinal} :
  (∃ β, β + 1 = α) ↔ α ≠ 0 := by
  constructor
  · rintro ⟨β, rfl⟩ e
    exact not_le_of_lt zero_lt_one (le_add_self.trans_eq e)
  · intro e
    cases le_or_gt Cardinal.aleph0 α with
    | inl h =>
      -- Using Cardinal.add_eq_right in place of cardinal.add_one_eq
      exact ⟨α, Cardinal.add_one_eq h⟩
    | inr h =>
      refine ⟨((α.toNat - 1) : _), ?_⟩
      rw [← bot_eq_zero, ← bot_lt_iff_ne_bot, bot_eq_zero,
        ← Cardinal.toNat_lt_iff_lt_of_lt_aleph0 _ h, Cardinal.zero_toNat, zero_lt_iff,
        ← Nat.one_le_iff_ne_zero] at e
      -- rwa [tsub_add_cancel_of_le e, Cardinal.cast_to_nat_of_lt_aleph0 h]
      -- rw [Nat.sub_add_cancel (le_of_lt this), Cardinal.cast_toNat_of_lt_aleph0 h]
      · sorry
      · exact e.trans h

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
      simp only [Set.insert_diff_singleton, Set.insert_eq_of_mem hx, e] at this
      rw [rank_span_set, ← Cardinal.add_one_inj];
      · exact this.symm
      · apply LinearIndependent.mono (fun _ h' ↦ h'.1) h
        -- Need to handle cardinal arithmetic
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, x ∉ p := by
      revert hp
      contrapose!
      rw [eq_top_iff]
      exact fun H x _ => H x
    obtain ⟨b, hbsub, hb⟩ := exists_linearIndependent R (p : Set M)
    have h : p = Submodule.span R b := p.span_eq ▸ hb.1.symm
    use insert x b; refine ⟨Cardinal.mk_insert (fun h ↦ hx (hbsub h)) ▸ ?_,
      LinearIndependent.insert hb.2 (h.symm ▸ hx)⟩
    · rw [h, rank_span_set hb.2]

lemma rankSuprNeTopAddOne {R : Type*} {M : Type*} [Field R] [AddCommGroup M] [Module R M] :
  (⨆ (p : Submodule R M) (h : p ≠ ⊤), Module.rank R p + 1) = Module.rank R M := by
  rw [ciSup_subtype''']
  · apply le_antisymm
    · -- First direction
      exact ciSup_le' (fun p ↦ add_one_le_dim_iff_exists_submodule_rank_eq.mpr ⟨p.1, p.2, rfl⟩)
    · by_cases h : Module.rank R M = 0
      · rw [h]; exact zero_le _
      · obtain ⟨α, hα⟩ := Cardinal.exists_add_one_eq_iff.mpr h
        have hpos : 1 ≤ Module.rank R M := Cardinal.one_le_iff_ne_zero.mpr h
        have : BddAbove (Set.range fun p : {x : Submodule R M // x ≠ ⊤} => Module.rank R p + 1) := by
          use Module.rank R M + 1
          rintro _ ⟨a, rfl⟩
          exact add_le_add (Submodule.rank_le _) rfl.le
        -- Rest of the proof
        exact hα.symm.le.trans (le_csupr this ⟨p, hp⟩)
  · use Module.rank R M + 1
    intro _ _
    exact add_le_add (Submodule.rank_le _) rfl.le
