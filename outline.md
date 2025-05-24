## proof outline

now we want to prove that amount of partitions of a finite set of
cardinality n is equal to (bell n)

steps:
1. define a function or proposition which counts amounts of
    partitions of a finite set of cardinality n
2. use strong induction on n to prove the equivalence between
   amount of partitions and bell numbers

proof sketch:
  1. ∅ has 1 partition (vacuous), singleton has 1 partition (trivial)
  2. for `n >= 1`, we can consider a set of size `n + 1`, pick an element from it,
     and consider the remaining n elements.
  3. for each `0 <= k < n` we can consider all possible subsets of
     cardinality k from the remaining n elements, meaning we have n choose k choices
  4. for each of these (distinct) choices, we can add the chosen element to that set, and get distinct partitions by adding that set (with the extra element) to every partition of the remaining `n - k` elements
  5. all the other possible partitions have the chosen element be in a singleton, so we consider `B_n` more partitions, with the singleton added
  6. so in total we have `B_n + sum_{k=0}^{n-1} (n choose k) * B_{n - k} = B_{n+1}` or, alternatively: `B_{n+1} = sum_{k=0}^{n} (n choose k) * B_k`


## previous attempt at bell termination-check

(get someone to help me fix it later)
```lean
  let r := Finset.range n
  let f (k : ℕ) (h: k ∈ r): ℕ :=
    have : k < n := by
    rw [Finset.mem_range] at h
    exact h
  Nat.choose n k * bell k
  r.sum f
```

## noncomputable but neatier instance of partition.Fintype

```lean
noncomputable instance partition.Fintype (X : Type) [DecidableEq X] (S: Finset X) : Fintype (partition X S) :=
  let β := { fam_cand : Finset (Finset X) // fam_cand ∈ S.powerset.powerset }

  let g : partition X S → β := fun part =>
    ⟨
      part.family,
      -- TODO: can this be simplified further?
      show part.family ∈ S.powerset.powerset by {
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
      }
    ⟩

  have g_inj : Function.Injective g := by {
    intros p q g_eq
    have families_eq : p.family = q.family := congr_arg Subtype.val g_eq
    ext
    · rw [families_eq]
  }

  Fintype.ofInjective g g_inj
```


## bell recurrence
```lean
-- Lemma stating the recurrence relation for Bell numbers (to be proven for user's `bell` def)
lemma bell_recurrence (n : ℕ) :
  bell (n + 1) = (Finset.range (n + 1)).sum (fun k => Nat.choose n k * bell k) :=
  by
    induction n with
    | zero =>
      simp [bell, bell_term]
    | succ n ih =>
      unfold bell
      rw [bell] at ih
      unfold bell_term
      rw [bell_term]
      simp [ih]
      rw [Finset.sum_range_succ]
      rw [bell_term] at ih
      simp [ih]
      simp [Finset.sum_range_succ]
      have : n.choose (n + 1) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        exact Nat.lt_succ_self n
      rw [this, zero_mul, zero_add] at ih
      rw [ih]
      rw [add_comm]
      let ih_term := ∑ k ∈ Finset.range (n + 1), n.choose k * bell k
      -- now I have a + b = c + b and I need to reduce it to a = c
      -- I need to cancel ih_term from both sides of the equation
      rw [add_right_cancel_iff]
      -- I now need to simplify
      /-
      match n, n with
      | 0, x => 1
      | x, 0 => 1
      | n.succ, k.succ => n.choose (k + 1) * bell_term (k + 1) k + bell_term (n + 1) k
      -/
      sorry
```
