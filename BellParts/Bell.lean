import BellParts.Partition
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


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
  rw [h_choose_zero, Nat.zero_mul]
  dsimp
  rw [Nat.zero_add]

lemma bell_eq_bell_term_succ_prev (x : ℕ) :
  bell (x+1) = bell_term (x+1) x :=
by
  rw [bell, bell_term_diag_simpl x]

lemma bell_term_recurrence (n k : ℕ) (h : k ≤ n) :
  bell_term (n+1) k = (Finset.range (k + 1)).sum (fun j => Nat.choose n j * bell j) :=
by
  induction k with
  | zero =>
    simp [bell, bell_term]
  | succ k ih =>
    have k_lt_n : k ≤ n := by linarith
    simp only [bell_term]
    have bell_to_term : bell_term (k + 1) k = bell (k + 1) :=
      (bell_eq_bell_term_succ_prev k).symm
    rw [bell_to_term, ih k_lt_n]
    nth_rewrite 2 [Finset.sum_range_succ]
    linarith

theorem bell_recurrence (n: ℕ) :
  bell (n + 1) = (Finset.range (n + 1)).sum (fun k => Nat.choose n k * bell k) :=
by
  rw [bell_eq_bell_term_succ_prev]
  simp only [le_refl, bell_term_recurrence]

instance this_should_have_been_synth
  (X: Type) [DecidableEq X]
  (S: Finset X):
  Fintype (Σ (s : S.powerset), partition X (S \ ↑s)) := by sorry

theorem bell_numbers_count_partitions
  (X : Type) [DecidableEq X] :
  ∀ n : ℕ, ∀ S : Finset X, S.card = n → finset_partition_count X S = bell n :=
by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    cases n with
    | zero =>
      have S_empty : S = ∅ := Finset.card_eq_zero.mp hS
      rw [S_empty]
      rw [finset_partition_count, bell, bell_term]
      rw [Fintype.card_eq_one_iff]
      use the_empty_partition X
      intro y
      exact partition.parts_of_empty_but_better y
    | succ n =>
      -- this depends on choice? maybe avoid choice if it does...
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hS]; exact Nat.zero_lt_succ n)
      let S' := S \ {x}
      have hS' : S'.card = n :=
      by
        rw [Finset.card_sdiff]
        · simp [hS]
        · exact Finset.singleton_subset_iff.mpr hx
      have S_eq : S = insert x S' :=
      by
        ext a
        simp [S', Finset.mem_sdiff]
        constructor
        · intro ha
          by_cases h : a = x
          · exact Or.inl h
          · exact Or.inr ⟨ha, h⟩
        · intro h
          cases h with
          | inl h => rw [h]; exact hx
          | inr h => exact h.1


      -- Apply the bijection
      rw [S_eq, finset_partition_count]
      have bij := partition.insert_recurrence S' x (by simp [S'])
      rw [Fintype.card_congr bij]

      rw [Fintype.card_sigma]

      -- Now use Bell recurrence
      conv_rhs => rw [← hS, ← hS', bell_recurrence]
      congr 1
      ext k
      simp only [Finset.sum_apply]

      -- Count subsets of size k
      have subset_count : (S'.powerset.filter (fun s => s.card = k)).card = Nat.choose n k := by
        sorry -- Standard counting argument

      -- For each subset s of size k, S' \ s has size n - k
      have : ∀ s ∈ S'.powerset, s.card = k → (S' \ s).card = n - k := by
        intro s hs hk
        rw [Finset.card_sdiff (Finset.mem_powerset.mp hs), hS', hk]

      -- Apply IH to each S' \ s
      sorry -- Complete the calculation


/-
  maybe this version could be cleaner to prove than to depend on cardinality?
  (it would need strong induction tho... Finset.induction_on'?)
  but then it's probably better to use one that depends on cardinality, for
  the purposes of equating that to bell numbers
-/
-- theorem bell_numbers_count_partitions
--   (X : Type)
--   [DecidableEq X]
--   (S : Finset X):
--   finset_partition_count X S = bell S.card :=
-- by
--   induction S using Finset.induction_on with
--   | empty =>
--     rw [
--       finset_partition_count,
--       bell,
--       Finset.card_empty,
--       bell_term,
--       Fintype.card_eq_one_iff,
--     ]
--     use the_empty_partition X
--     intro y
--     exact partition.parts_of_empty_but_better y
--   | insert x S x_not_in_S ih =>
--     rw [
--       Finset.card_insert_of_not_mem,
--       bell_eq_bell_term_succ_prev,
--       bell_term_recurrence
--     ]
--     unfold finset_partition_count
--     have h : (Finset.range (S.card + 1)).sum (fun k => Nat.choose S.card k * bell k) = bell (S.card + 1):= by
--       rw [bell_recurrence]
