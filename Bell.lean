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

-- from data.setoid.partitions
-- youtu.be/FEKsZj3WkTY
@[ext] structure partition (X : Type u) [DecidableEq X] (S: Finset X) where
  family : Finset (Finset X)
  non_empty: ∀ c ∈ family, c ≠ ∅
  covers: family.biUnion id = S
  disjoint: ∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d

def partition.mk_if_valid {X: Type} [DecidableEq X] (S : Finset X) (family : Finset (Finset X)) : Option (partition X S) :=
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
lemma partition.mk_if_valid_id_family {X : Type}
  [DecidableEq X]
  (S : Finset X)
  (fam : Finset (Finset X))
  (part : partition X S)
  (mk_is_some : partition.mk_if_valid S fam = some part) :
  part.family = fam := by
    unfold partition.mk_if_valid at mk_is_some
    split_ifs at mk_is_some with h₁ h₂ h₃ <;> simp only [Option.some_inj] at mk_is_some
    rw [← mk_is_some]

instance partition.Fintype {X : Type} [DecidableEq X] (S: Finset X) : Fintype (partition X S) where
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

/-
now we want to prove that amount of partitions of a finite set of
cardinality n is equal to (bell n)

steps:
1. define a function or proposition which counts amounts of
    partitions of a finite set of cardinality n
2. use strong induction on n to prove the equivalence between
   amount of partitions and bell numbers

proof sketch:
  1. ∅ has 1 partition (vacuous), singleton has 1 partition (trivial)
  2. for n >= 1, we can consider a set of size n + 1, pick an element from it,
     and consider the remaining n elements.
  3. for each 0 <= k < n we can consider all possible subsets of
     cardinality k from the remaining n elements, meaning we have n choose k
     choices
  4. for each of these (distinct) choices, we can add the chosen element to that set,
     and get distinct partitions by adding that set (with the extra element) to every
     partition of the remaining n - k elements
  5. all the other possible partitions have the chosen element be in a singleton,
     so we consider B_n more partitions, with the singleton added
  6. so in total we have B_n + sum_{k=0}^{n-1} (n choose k) * B_{n - k} = B_{n+1} or,
     alternatively: B_{n+1} = sum_{k=0}^{n} (n choose k) * B_k
-/



/-

-/
-- def partitions_size (X: Type) [DecidableEq X] : ℕ := Finset.univ.card (partition X)
-- def partitions_size { X: Type u } [DecidableEq X]  (S: Finpartition X): ℕ :=
--   Fintype.card (partition S)

-- def partitions_count {α : Type u_1} [Lattice α] [OrderBot α] [Fintype α] (a: α) : ℕ :=
--   Fintype.card (Finpartition a)
def count_partitions_of_finset (X : Type u) [DecidableEq X] (S : Finset X) : ℕ :=
  Fintype.card (partition X S)

/- previous attempt (get someone to help me fix it later)
  let r := Finset.range n
  let f (k : ℕ) (h: k ∈ r): ℕ :=
    have : k < n := by
    rw [Finset.mem_range] at h
    exact h
  Nat.choose n k * bell k
  r.sum f
-/
