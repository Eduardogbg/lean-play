import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

lemma filterMap_filter_isSome_eq_filterMap
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α)
  (f : α → Option β)
  (hf_inj : ∀ (a a' : α), ∀ (b : β), (f a = some b) → (f a' = some b) → a = a')
: ((s.filter (fun x => (f x).isSome)).filterMap f hf_inj) = s.filterMap f hf_inj :=
by
  have filterMap_subset_filter_isSome_filterMap:
    (s.filterMap f hf_inj) ⊆ (s.filter (fun x => (f x).isSome)).filterMap f hf_inj :=
  by
    intro y y_in_filterMap
    rw [Finset.mem_filterMap] at y_in_filterMap
    rcases y_in_filterMap with ⟨x, x_in_s, fx_is_some_y⟩
    rw [Finset.mem_filterMap]
    use x
    constructor
    .
      rw [Finset.mem_filter]
      constructor
      . exact x_in_s
      . simp only [Option.isSome_some, fx_is_some_y]
    . exact fx_is_some_y

  have filter_isSome_filterMap_subset_filterMap:
    (s.filter (fun x => (f x).isSome)).filterMap f hf_inj ⊆ s.filterMap f hf_inj :=
  by
    intro y y_in_filterMap
    rw [Finset.mem_filterMap] at y_in_filterMap
    rcases y_in_filterMap with ⟨x, x_in_s_filter_isSome, fx_is_some_y⟩
    rw [Finset.mem_filterMap]
    use x
    constructor
    .
      rw [Finset.mem_filter] at x_in_s_filter_isSome
      exact And.left x_in_s_filter_isSome
    . exact fx_is_some_y

  apply Finset.Subset.antisymm_iff.mpr
  constructor
  . exact filter_isSome_filterMap_subset_filterMap
  . exact filterMap_subset_filter_isSome_filterMap

lemma filterMap_card_eq_filter_isSome_card
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α)
  (f : α → Option β)
  (hf_inj : ∀ (a a' : α), ∀ (b : β), (f a = some b) → (f a' = some b) → a = a')
 : (s.filterMap f hf_inj).card = (s.filter (fun x => (f x).isSome)).card :=
by
  rw [Finset.card_bij (fun x _ => Option.get (f x) _)]
  -- prove the function maps to the target set
  ·
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨x_in_s, fx_isSome⟩ := hx
    rw [Finset.mem_filterMap]
    use x, x_in_s
    simp only [Option.some_get fx_isSome]
  -- prove injectivity
  ·
    intro x₁ hx₁ x₂ hx₂ h_eq
    rw [Finset.mem_filter] at hx₁ hx₂
    obtain ⟨x₁_in_s, x₁_isSome⟩ := hx₁
    obtain ⟨x₂_in_s, x₂_isSome⟩ := hx₂
    have h₁ : f x₁ = some (Option.get (f x₁) x₁_isSome) := by simp only [Option.some_get x₁_isSome]
    have h₂ : f x₂ = some (Option.get (f x₂) x₂_isSome) := by simp only [Option.some_get x₂_isSome]
    simp [Option.get_inj] at h_eq
    apply hf_inj x₁ x₂ (Option.get (f x₁) x₁_isSome)
    · simp only [Option.some_get x₁_isSome]
    · simp only [Option.some_get x₂_isSome, h_eq]
  -- prove surjectivity
  ·
    intro y hy
    rw [Finset.mem_filterMap] at hy
    obtain ⟨x, hx_in_s, hfx⟩ := hy
    use x
    constructor
    · simp only [hfx, Option.get_some]
    ·
      rw [Finset.mem_filter]
      constructor
      · exact hx_in_s
      · rw [hfx]
        exact Option.isSome_some
  -- prove the function is well-defined (implicit argument)
  .
    intro x x_in_filter
    rw [Finset.mem_filter] at x_in_filter
    exact And.right x_in_filter
