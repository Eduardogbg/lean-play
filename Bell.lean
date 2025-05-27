import mathlib
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
import Mathlib.Logic.Equiv.Option


def bell_term: ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | n+1, k+1 =>
    have term := Nat.choose n (k + 1) * bell_term (k + 1) k
    have rest := bell_term (n + 1) k
    term + rest

def bell (n : ℕ) : ℕ := bell_term n n

lemma bell_term_diag_simpl (x : ℕ) :
  bell_term (x+1) (x+1) = bell_term (x+1) x :=
by
  simp only [bell_term]
  unfold bell_term
  have h_choose_zero : Nat.choose x (x+1) = 0 := by
    apply Nat.choose_eq_zero_of_lt
    exact Nat.lt_succ_self x
  rw [h_choose_zero, zero_mul]
  dsimp
  rw [zero_add]

lemma bell_eq_bell_term_succ_prev (x : ℕ) :
  bell (x+1) = bell_term (x+1) x :=
by
  rw [bell, bell_term_diag_simpl x]


-- from data.setoid.partitions
-- youtu.be/FEKsZj3WkTY
@[ext] structure partition (X : Type u) [DecidableEq X] (S: Finset X) where
  family : Finset (Finset X)
  non_empty: ∀ c ∈ family, c ≠ ∅
  covers: family.biUnion id = S
  disjoint: ∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d

def partition.mk_if_valid {X: Type u} [DecidableEq X] (S: Finset X) (family: Finset (Finset X)) : Option (partition X S) :=
  if non_empty : (∀ c ∈ family, c ≠ ∅)
  then if covers : (family.biUnion id = S)
       then if disjoint : (∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d)
            then some {
              family := family,
              non_empty := non_empty,
              covers := covers,
              disjoint := disjoint
            }
            else none
       else none
  else none

-- TODO: how to name this?
lemma partition.mk_if_valid_id_family
  {X: Type u}
  [DecidableEq X]
  (S: Finset X)
  (fam: Finset (Finset X))
  (part: partition X S)
  (mk_is_some: partition.mk_if_valid S fam = some part):
  part.family = fam :=
  by
    unfold partition.mk_if_valid at mk_is_some
    split_ifs at mk_is_some with h₁ h₂ h₃; simp only [Option.some_inj] at mk_is_some
    rw [← mk_is_some]


lemma partition.mk_if_valid_inj_some {X: Type u} [DecidableEq X] (S: Finset X) :
  ∀ (a a' : Finset (Finset X)), ∀ b ∈ mk_if_valid S a, b ∈ mk_if_valid S a' → a = a' :=
by
  intros fam1 fam2 p p_in_fam1 p_in_fam2
  rw [Option.mem_def] at p_in_fam1 p_in_fam2

  have fam_eq_fam1 : p.family = fam1 :=
    partition.mk_if_valid_id_family S fam1 p p_in_fam1
  have fam_eq_fam2 : p.family = fam2 :=
    partition.mk_if_valid_id_family S fam2 p p_in_fam2

  rw [← fam_eq_fam1, fam_eq_fam2]

-- not the shortest neatier proof but it's constructive and educational
instance partition.Fintype {X : Type u} [DecidableEq X] (S: Finset X) : Fintype (partition X S) where
  elems := (S.powerset.powerset).filterMap (partition.mk_if_valid S) (partition.mk_if_valid_inj_some S)
  complete := by
    intro part
    simp_rw [Finset.mem_filterMap]
    use part.family
    constructor
    ·
      rw [Finset.mem_powerset]
      intro c c_in_fam
      rw [Finset.mem_powerset]
      intro x x_in_c
      have x_in_union : x ∈ part.family.biUnion (id : Finset X → Finset X) := by
        apply Finset.mem_biUnion.mpr
        use c
        constructor
        · exact c_in_fam
        · exact x_in_c
      rw [part.covers] at x_in_union
      exact x_in_union
    ·
      unfold partition.mk_if_valid
      split_ifs with non_empty covers disjoint
      · apply Option.some_inj.mpr
        ext
        · rfl
      · exact disjoint part.disjoint
      . exact covers part.covers
      . exact non_empty part.non_empty

def finset_partition_count (X : Type u) [DecidableEq X] (S : Finset X): ℕ :=
  Fintype.card (partition X S)

lemma finset_partition_count_recurrence
  {X : Type u} [DecidableEq X] [Inhabited X]
  (n : ℕ)
  (S : Finset X)
  (s_card : S.card = n + 1) :
  finset_partition_count X S =
    (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k *
      (finset_partition_count X
        (Finset.empty.image (fun (_ : Finset.range (n - k)) => default) )
      )
    ) :=
  by
    sorry

def the_empty_partition (X : Type u) [DecidableEq X] : partition X ∅ := {
  family := ∅,
  non_empty := fun c hc => (Finset.not_mem_empty c hc).elim
  covers := Finset.biUnion_empty
  disjoint := fun c hc => (Finset.not_mem_empty c hc).elim
}

lemma singleton_empty_powerset {X} [DecidableEq X]: ({∅}: (Finset (Finset X))).powerset = {∅, {∅}} := by
  ext fam
  constructor
  · intro h
    exact h
  · intro h
    exact h

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

lemma partitions_of_empty  {X: Type u} [Inhabited X] [DecidableEq X] :
  Finset.filterMap
    (partition.mk_if_valid ∅)
    { ∅, {∅} }
    (partition.mk_if_valid_inj_some ∅)
  = {the_empty_partition X} :=
by
  ext part
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_iff_left_iff_imp, iff_def]
  constructor
  · intro fam_part_if_valid
    ext
    constructor
    . intros a_in_fam
      rw [the_empty_partition]
      simp only [Finset.not_mem_empty]
      have : part.family = ∅ :=
      by
        unfold partition.mk_if_valid at fam_part_if_valid
        rw [Finset.mem_filterMap] at fam_part_if_valid
        rcases fam_part_if_valid with ⟨x, x_partition_if_valid⟩
        rcases x_partition_if_valid with ⟨x_in_powerset, x_part_if_valid⟩
        split_ifs at x_part_if_valid with non_empty covers disjoint
        rw [Option.some_inj] at x_part_if_valid
        simp only [Finset.mem_insert, Finset.mem_singleton] at x_in_powerset
        have x_empty_set : x = ∅ := by
          rcases x_in_powerset with (rfl | x_in_powerset)
          . exact rfl
          .
            exfalso
            apply absurd non_empty
            simp only [ne_eq, Finset.forall_mem_not_eq', Decidable.not_not]
            rw [x_in_powerset]
            rw [Finset.mem_singleton]
        obtain ⟨_, _⟩ := x_part_if_valid
        simp only [x_empty_set]
      apply absurd a_in_fam
      rw [this]
      simp only [Finset.not_mem_empty, not_false_eq_true]
    unfold the_empty_partition
    simp only [Finset.not_mem_empty, IsEmpty.forall_iff]
  .
    -- TODO: this should be trivialer
    intro part_empty
    rcases part_empty with ⟨_, _⟩
    unfold partition.mk_if_valid
    rw [Finset.mem_filterMap]
    use ∅
    constructor
    . simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    .
      split_ifs with non_empty covers disjoint
      rw [Option.some_inj]
      unfold the_empty_partition
      rfl
      .
        simp only [Finset.not_mem_empty, IsEmpty.forall_iff] at disjoint
        rw [implies_true, not_true_eq_false] at disjoint
        exact disjoint
      . simp only [Finset.biUnion_empty, not_true_eq_false] at covers
      .
        simp only [Finset.not_mem_empty, ne_eq, IsEmpty.forall_iff] at non_empty
        rw [implies_true, not_true_eq_false] at non_empty
        exact non_empty

lemma card_partitions_of_empty {X: Type u} [Inhabited X] [DecidableEq X] :
  Fintype.card (partition X ∅) = 1 :=
by
  unfold Fintype.card
  unfold Finset.univ
  unfold Fintype.elems
  unfold partition.Fintype
  simp only [Finset.powerset_empty]
  rw [singleton_empty_powerset, partitions_of_empty]
  unfold the_empty_partition
  rw [Finset.card_singleton]

theorem bell_numbers_count_partitions
  (X : Type u)
  [DecidableEq X]
  (S : Finset X):
  finset_partition_count X S = bell S.card :=
  by
    sorry
