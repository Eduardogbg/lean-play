import mathlib
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic -- For Nat.choose
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

-- not the shortest neatier proof but it's constructive and educational
instance partition.Fintype {X : Type u} [DecidableEq X] (S: Finset X) : Fintype (partition X S) where
  elems := (S.powerset.powerset).filterMap (partition.mk_if_valid S) (
    by
      intros fam1 fam2 p p_in_fam1 p_in_fam2
      rw [Option.mem_def] at p_in_fam1 p_in_fam2

      have fam_eq_fam1 : p.family = fam1 :=
        partition.mk_if_valid_id_family S fam1 p p_in_fam1
      have fam_eq_fam2 : p.family = fam2 :=
        partition.mk_if_valid_id_family S fam2 p p_in_fam2

      rw [← fam_eq_fam1, fam_eq_fam2]
  )
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

lemma empty_powerset {X} [DecidableEq X]: (∅: Finset X).powerset = {∅} := by
  ext fam
  constructor
  · intro h
    exact h
  · intro h
    exact h

lemma empty_singleton_powerset {X} [DecidableEq X]: ({∅}: (Finset (Finset X))).powerset = {∅, {∅}} := by
  ext fam
  constructor
  · intro h
    exact h
  · intro h
    exact h

lemma empty_double_powerset {X} [DecidableEq X]: (∅: Finset X).powerset.powerset = {∅, {∅}} := by
  rw [empty_powerset, empty_singleton_powerset]

lemma card_empty_partition {X: Type u} [DecidableEq X] : Fintype.card (partition X ∅) = 1 :=
by
  unfold Fintype.card Finset.univ partition.Fintype
  let ppe := (∅: Finset X).powerset.powerset
  have h : Finset.filter (fun fam => (partition.mk_if_valid ∅ fam).isSome) (∅: Finset X).powerset.powerset = {∅} := by
    rw [empty_double_powerset]
    ext fam
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_iff_left_iff_imp, iff_def]
    constructor
    · intro h_conj
      rcases h_conj with ⟨h_fam_cases, h_is_some⟩
      cases h_fam_cases with
      | inl h_fam_is_empty_family => exact h_fam_is_empty_family
      | inr h_fam_contains_empty_set =>
        have h_eval_invalid : (partition.mk_if_valid (∅ : Finset X) ({∅} : Finset (Finset X))).isSome = false := by
          unfold partition.mk_if_valid
          simp only [ne_eq, not_true, false_implies, Option.isSome_none]
          simp
        rw [h_fam_contains_empty_set] at h_is_some
        rw [h_eval_invalid] at h_is_some
        apply absurd h_is_some
        -- TODO: figure out which tactics were used here
        simp
    ·
      intro h_fam_empty
      rw [h_fam_empty]
      simp only [true_or, true_and]
      unfold partition.mk_if_valid
      simp only [Finset.not_mem_empty, implies_true, Finset.biUnion_empty, id_eq, true_and, forall_const, imp_self, Option.isSome_some]
      -- TODO: figure out which tactics were used here
      simp
  unfold Fintype.elems
  simp
  rw [empty_double_powerset] at h
  rw [empty_singleton_powerset]
  rw [Finset.filterMap]
  sorry



theorem bell_numbers_count_partitions
  (X : Type u)
  [DecidableEq X]
  (S : Finset X):
  finset_partition_count X S = bell S.card :=
  by
    sorry
